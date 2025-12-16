/**
@file   Reflector.cpp
@brief  The main reflector class
@author Tobias Blomberg / SM0SVX
@date   2017-02-11

\verbatim
SvxReflector - An audio reflector for connecting SvxLink Servers
Copyright (C) 2003-2025 Tobias Blomberg / SM0SVX

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
\endverbatim
*/

/****************************************************************************
 *
 * System Includes
 *
 ****************************************************************************/

#include <cassert>
#include <unistd.h>
#include <algorithm>
#include <fstream>
#include <iterator>
#include <regex>
#include <stdexcept>  // <-- hinzugefügt für Parsing-Ausnahmen
#include <map>        // <-- hinzugefügt für Blocklisten-Persistenz
#include <limits>     // <-- hinzugefügt für UINT64_MAX (permanent block)
#include <memory>     // <-- für std::unique_ptr beim JSON-Schreiben
#include <unordered_set> // <-- Userlist-Reload + QSY_DENY
#include <sstream>       // <-- Stringstreams für Loader
#include <ctime>

/****************************************************************************
 *
 * Project Includes
 *
 ****************************************************************************/

#include <AsyncConfig.h>
#include <AsyncTcpServer.h>
#include <AsyncDigest.h>
#include <AsyncSslCertSigningReq.h>
#include <AsyncEncryptedUdpSocket.h>
#include <AsyncApplication.h>
#include <AsyncPty.h>

#include <common.h>
#include <config.h>


/****************************************************************************
 *
 * Local Includes
 *
 ****************************************************************************/

#include "Reflector.h"
#include "ReflectorClient.h"
#include "TGHandler.h"


/****************************************************************************
 *
 * Namespaces to use
 *
 ****************************************************************************/

using namespace std;
using namespace Async;



/****************************************************************************
 *
 * Defines & typedefs
 *
 ****************************************************************************/

#define RENEW_AFTER 2/3


/****************************************************************************
 *
 * Local class definitions
 *
 ****************************************************************************/



/****************************************************************************
 *
 * Local functions
 *
 ****************************************************************************/

namespace {
  bool ensureDirectoryExist(const std::string& path)
  {
    std::vector<std::string> parts;
    SvxLink::splitStr(parts, path, "/");
    std::string dirname;
    if (path[0] == '/')
    {
      dirname = "/";
    }
    else if (path[0] != '.')
    {
      dirname = "./";
    }
    if (path.back() != '/')
    {
      parts.erase(std::prev(parts.end()));
    }
    for (const auto& part : parts)
    {
      dirname += part + "/";
      if (access(dirname.c_str(), F_OK) != 0)
      {
        std::cout << "Create directory '" << dirname << "'" << std::endl;
        if (mkdir(dirname.c_str(), 0777) != 0)
        {
          std::cerr << "*** ERROR: Could not create directory '"
                    << dirname << "'" << std::endl;
          return false;
        }
      }
    }
    return true;
  } /* ensureDirectoryExist */


  void startCertRenewTimer(const Async::SslX509& cert, Async::AtTimer& timer)
  {
    int days=0, seconds=0;
    cert.validityTime(days, seconds);
    time_t renew_time = cert.notBefore() +
        (static_cast<time_t>(days)*24*3600 + seconds)*RENEW_AFTER;
    timer.setTimeout(renew_time);
    timer.setExpireOffset(10000);
    timer.start();
  } /* startCertRenewTimer */
};

/****************************************************************************
 *
 * Persistente Blockliste (global in dieser Übersetzungseinheit)
 *
 ****************************************************************************/

namespace {

  // Datei-Pfad zur Blockliste (per Konfig übersteuerbar)
  std::string g_blocked_file;

  // Callsign -> Unix-Epoch bis wann geblockt (UINT64_MAX == permanent)
  std::map<std::string, uint64_t> g_blocked_until_epoch;

  // Nach Entsperren: einmalige Benachrichtigung beim nächsten UDP-Paket
  std::map<std::string, uint64_t> g_unblock_notice_until;

  inline uint64_t nowEpoch()
  {
    return static_cast<uint64_t>(std::time(nullptr));
  }

  bool saveBlockedList()
  {
    Json::Value root(Json::objectValue);
    Json::Value arr(Json::arrayValue);

    for (const auto& kv : g_blocked_until_epoch)
    {
      const auto& cn = kv.first;
      const uint64_t until = kv.second;

      Json::Value entry(Json::objectValue);
      entry["callsign"] = cn;

      if (until == std::numeric_limits<uint64_t>::max())
      {
        entry["permanent"] = true;
      }
      else
      {
        entry["permanent"] = false;
        entry["until"] = Json::UInt64(until);
      }

      arr.append(entry);
    }

    root["blocked"] = arr;

    if (g_blocked_file.empty())
    {
      std::cerr << "*** ERROR: BLOCKLIST_FILE path is empty.\n";
      return false;
    }

    if (!ensureDirectoryExist(g_blocked_file))
    {
      std::cerr << "*** ERROR: Cannot ensure directory for '"
                << g_blocked_file << "'.\n";
      return false;
    }

    std::ofstream ofs(g_blocked_file, std::ios::trunc);
    if (!ofs.good())
    {
      std::cerr << "*** ERROR: Cannot open '" << g_blocked_file
                << "' for writing. Permission denied?\n";
      return false;
    }

    Json::StreamWriterBuilder b;
    b["indentation"] = "  ";
    std::unique_ptr<Json::StreamWriter> w(b.newStreamWriter());
    w->write(root, &ofs);
    return ofs.good();
  }

  bool loadBlockedList()
  {
    g_blocked_until_epoch.clear();

    if (g_blocked_file.empty())
      return false;

    std::ifstream ifs(g_blocked_file, std::ios::in | std::ios::binary);
    if (!ifs.good())
    {
      // Datei fehlt -> später Default schreiben, kein Fehler
      return true;
    }

    std::string content((std::istreambuf_iterator<char>(ifs)),
                        std::istreambuf_iterator<char>());

    if (content.empty())
    {
      std::cerr << "*** WARNING: Blocklist file '" << g_blocked_file
                << "' is empty. Using default {\"blocked\":[]}.\n";
      (void)saveBlockedList();
      return true;
    }

    Json::CharReaderBuilder rb;
    rb["collectComments"] = false;
    std::string errs;
    Json::Value root;

    std::unique_ptr<Json::CharReader> reader(rb.newCharReader());
    const char* begin = content.data();
    const char* end   = begin + content.size();
    const bool ok = reader->parse(begin, end, &root, &errs);

    if (!ok || !root.isObject() || !root.isMember("blocked") || !root["blocked"].isArray())
    {
      std::cerr << "*** WARNING: Failed to parse '" << g_blocked_file
                << "': " << (errs.empty() ? "invalid content" : errs)
                << ". Resetting to default {\"blocked\":[]}.\n";
      g_blocked_until_epoch.clear();
      (void)saveBlockedList();
      return true;
    }

    const auto& arr = root["blocked"];
    for (const auto& it : arr)
    {
      if (!it.isObject()) continue;
      const auto cn = it.get("callsign", "").asString();
      if (cn.empty()) continue;

      const bool perm = it.get("permanent", false).asBool();
      uint64_t until = perm ? std::numeric_limits<uint64_t>::max()
                            : static_cast<uint64_t>(it.get("until", 0).asUInt64());

      if (until == std::numeric_limits<uint64_t>::max() ||
          until > static_cast<uint64_t>(std::time(nullptr)))
      {
        g_blocked_until_epoch[cn] = until;
      }
    }
    return true;
  }

  // Auf aktiven Client anwenden (falls verbunden)
  void applyBlockForCallsign(const std::string& cn)
  {
    auto it = g_blocked_until_epoch.find(cn);
    if (it == g_blocked_until_epoch.end()) return;

    uint64_t until = it->second;
    auto client = ReflectorClient::lookup(cn);
    if (!client) return;

    if (until == std::numeric_limits<uint64_t>::max())
    {
      client->setBlock(ReflectorClient::PERM_BLOCKTIME);
      client->sendMsg(MsgError("You are permanently blocked for some reason - please contact Admin Team!"));
    }
    else
    {
      auto now = nowEpoch();
      if (until <= now)
      {
        g_blocked_until_epoch.erase(it);
        (void)saveBlockedList();
        return;
      }
      unsigned secs = static_cast<unsigned>(until - now);
      client->setBlock(secs);
      client->sendMsg(MsgError(std::string("You are blocked for ")
                               + std::to_string(secs) + " seconds for some reason - Please contact Admin Team!"));
    }
  }

} // anonymous namespace (Blockliste)

/****************************************************************************
 *
 * Userlisten-Loader & Live-Reload + QSY-Deny + TG-Handling
 *
 ****************************************************************************/

namespace {

  // Merkt sich, welche Keys beim letzten Laden gesetzt wurden
  std::unordered_set<std::string> g_userlist_prev_keys_dl;
  std::unordered_set<std::string> g_userlist_prev_keys_ww;

  // QSY-Deny-Liste: Calls, die kein QSY auslösen dürfen
  std::string g_qsy_deny_file;
  std::unordered_set<std::string> g_qsy_deny_callsigns;

  // TG-Handling-Datei (externe TG-Definitionen)
  std::string g_tg_handling_file;

  inline void trim(std::string& s) {
    auto l = s.find_first_not_of(" \t\r\n");
    auto r = s.find_last_not_of(" \t\r\n");
    if (l == std::string::npos) { s.clear(); return; }
    s = s.substr(l, r - l + 1);
  }

  static std::string sliceByMarkers(const std::string& content,
                                    const std::string& beginMarker,
                                    const std::string& endMarker)
  {
    if (beginMarker.empty() || endMarker.empty())
      return content;
    auto b = content.find(beginMarker);
    auto e = content.find(endMarker);
    if (b == std::string::npos || e == std::string::npos || e < b)
      return content;
    e += endMarker.size();
    return content.substr(b, e - b);
  }

  static std::unordered_set<std::string>
  parseKeyValuesIntoConfig(Async::Config& cfg,
                           const std::string& section,
                           const std::string& text)
  {
    std::unordered_set<std::string> loaded;
    std::istringstream is(text);
    std::string line;
    while (std::getline(is, line)) {
      std::string s = line;
      trim(s);
      if (s.empty()) continue;
      if (s[0] == '#') continue;           // Kommentare überspringen

      // Sektionen ([USERS]) jetzt zulassen:
      // früher: if (s.rfind("[", 0) == 0) continue;

      auto eq = s.find('=');
      if (eq == std::string::npos) continue;

      std::string key = s.substr(0, eq);
      std::string val = s.substr(eq + 1);
      trim(key);
      trim(val);

      if (key.empty()) continue;

      cfg.setValue(section, key, val);
      loaded.insert(key);
    }
    return loaded;
  }

  static bool reloadOneUserFile(Async::Config& cfg,
                                const std::string& file,
                                const std::string& section,
                                const std::string& beginMarker,
                                const std::string& endMarker,
                                std::unordered_set<std::string>& prevKeys)
  {
    // Leerer Dateipfad – nur warnen, Semantik beibehalten (true zurück)
    if (file.empty()) {
      std::cerr << "[USERLIST] Reload: empty file path given\n";
      return true;
    }

    std::ifstream in(file);
    if (!in.good()) {
      std::cerr << "*** WARNING: USERLIST reload: cannot open '" << file << "'\n";
      // Semantik beibehalten: true zurückgeben, damit Gesamt-OK nicht kippt
      return true;
    }

    std::string content((std::istreambuf_iterator<char>(in)),
                         std::istreambuf_iterator<char>());
    std::string sliced = sliceByMarkers(content, beginMarker, endMarker);
    auto newly = parseKeyValuesIntoConfig(cfg, section, sliced);

    std::cout << "[USERLIST] Parsed " << newly.size()
              << " entries from '" << file << "'" << std::endl;

    size_t removed = 0;
    for (const auto& k : prevKeys) {
      if (newly.find(k) == newly.end()) {
        cfg.setValue(section, k, ""); // neutralisieren (kein unset verfügbar)
        ++removed;
      }
    }

    if (removed > 0) {
      std::cout << "[USERLIST] Removed " << removed
                << " stale keys for section '" << section
                << "' from '" << file << "'" << std::endl;
    }

    std::cout << "[USERLIST] Reload done: file='" << file << "'" << std::endl;

    prevKeys = std::move(newly);
    return true;
  }

  static bool reloadAllUserLists(Async::Config& cfg)
  {
    std::string section = "USERS";
    (void)cfg.getValue("GLOBAL", "USERLIST_SECTION", section);

    // Default-Pfade, durch Konfiguration überschreibbar
    std::string dlFile = "svxreflector.d/users_dl.conf";
    std::string wwFile = "svxreflector.d/users_ww.conf";
    (void)cfg.getValue("GLOBAL", "USERLIST_FILE_DL", dlFile);
    (void)cfg.getValue("GLOBAL", "USERLIST_FILE_WW", wwFile);

    // Marker bewusst ignorieren: leere Strings => sliceByMarkers() liefert vollen Inhalt
    const std::string noMarker;

    std::cout << "[USERLIST] Reload ALL start: section='" << section
              << "', dlFile='" << dlFile
              << "', wwFile='" << wwFile << "'" << std::endl;

    bool ok = true;

    std::cout << "[USERLIST] Reload DL: '" << dlFile << "'" << std::endl;
    bool r1 = reloadOneUserFile(cfg, dlFile, section, noMarker, noMarker, g_userlist_prev_keys_dl);
    std::cout << "[USERLIST] Reload DL done, ok=" << (r1 ? "true" : "false") << std::endl;
    ok &= r1;

    std::cout << "[USERLIST] Reload WW: '" << wwFile << "'" << std::endl;
    bool r2 = reloadOneUserFile(cfg, wwFile, section, noMarker, noMarker, g_userlist_prev_keys_ww);
    std::cout << "[USERLIST] Reload WW done, ok=" << (r2 ? "true" : "false") << std::endl;
    ok &= r2;

    std::cout << "[USERLIST] Reload ALL done, ok=" << (ok ? "true" : "false") << std::endl;
    return ok;
  }

  // --------- QSY-Deny-Liste ---------

  bool loadQsyDenyList(const std::string& file)
  {
    g_qsy_deny_callsigns.clear();

    if (file.empty()) {
      std::cerr << "[QSY_DENY] No file configured\n";
      return false;
    }

    std::ifstream in(file);
    if (!in.good()) {
      std::cerr << "*** WARNING: QSY_DENY: cannot open '" << file << "'\n";
      return false;
    }

    std::string line;
    while (std::getline(in, line)) {
      trim(line);
      if (line.empty()) continue;
      if (line[0] == '#') continue;
      if (line.front() == '[' && line.back() == ']') continue;

      std::transform(line.begin(), line.end(), line.begin(), ::toupper);
      g_qsy_deny_callsigns.insert(line);
    }

    std::cout << "[QSY_DENY] Loaded " << g_qsy_deny_callsigns.size()
              << " entries from '" << file << "'" << std::endl;
    return true;
  }

  inline bool isQsyDenied(const std::string& cs)
  {
    if (cs.empty()) return false;
    std::string tmp = cs;
    std::transform(tmp.begin(), tmp.end(), tmp.begin(), ::toupper);
    return (g_qsy_deny_callsigns.find(tmp) != g_qsy_deny_callsigns.end());
  }

  bool qsyAllowedForClient(ReflectorClient* client)
  {
    if (client == nullptr) return false;

    const std::string& cs = client->callsign();
    if (!isQsyDenied(cs)) {
      return true;
    }

    std::cout << cs << ": QSY denied (callsign in qsy_deny.conf)" << std::endl;

    return false;
  }

  // --------- TG-Handling aus externer Datei ---------

  bool loadTgHandlingFile(Async::Config& cfg, const std::string& file)
  {
    if (file.empty()) {
      std::cerr << "[TG] No TG_HANDLING_FILE configured\n";
      return false;
    }

    std::ifstream in(file);
    if (!in.good()) {
      std::cerr << "*** WARNING: TG: cannot open '" << file << "'\n";
      return false;
    }

    std::string line;
    std::string current_section;
    unsigned entries = 0;

    while (std::getline(in, line)) {
      std::string s = line;
      trim(s);
      if (s.empty()) continue;
      if (s[0] == '#') continue;

      // Neue Sektion: [TG#1], [TG#2], ...
      if (s.front() == '[' && s.back() == ']') {
        current_section = s.substr(1, s.size() - 2);
        trim(current_section);
        continue;
      }

      // Nur key=value Zeilen, wenn wir in einer TG-Sektion sind
      auto eq = s.find('=');
      if (eq == std::string::npos) continue;
      if (current_section.empty()) continue;

      std::string key = s.substr(0, eq);
      std::string val = s.substr(eq + 1);
      trim(key);
      trim(val);
      if (key.empty()) continue;

      cfg.setValue(current_section, key, val);
      ++entries;
    }

    std::cout << "[TG] Loaded " << entries
              << " entries from '" << file << "'" << std::endl;
    return true;
  }

} // namespace (Userlisten + QSY-Deny + TG-Handling)

/****************************************************************************
 *
 * Exported Global Variables
 *
 ****************************************************************************/



/****************************************************************************
 *
 * Local Global Variables
 *
 ****************************************************************************/

namespace {
  ReflectorClient::ProtoVerRangeFilter v1_client_filter(
      ProtoVer(1, 0), ProtoVer(1, 999));
  ReflectorClient::ProtoVerLargerOrEqualFilter ge_v2_client_filter(
      ProtoVer(2, 0));
};


/****************************************************************************
 *
 * Public static functions
 *
 ****************************************************************************/

time_t Reflector::timeToRenewCert(const Async::SslX509& cert)
{
  if (cert.isNull())
  {
    return 0;
  }

  int days=0, seconds=0;
  cert.validityTime(days, seconds);
  time_t renew_time = cert.notBefore() +
    (static_cast<time_t>(days)*24*3600 + seconds)*RENEW_AFTER;
  return renew_time;
} /* Reflector::timeToRenewCert */


/****************************************************************************
 *
 * Public member functions
 *
 ****************************************************************************/

Reflector::Reflector(void)
  : m_srv(0), m_udp_sock(0), m_tg_for_v1_clients(1), m_random_qsy_lo(0),
    m_random_qsy_hi(0), m_random_qsy_tg(0), m_http_server(0), m_cmd_pty(0),
    m_keys_dir("private/"), m_pending_csrs_dir("pending_csrs/"),
    m_csrs_dir("csrs/"), m_certs_dir("certs/"), m_pki_dir("pki/")
{
  TGHandler::instance()->talkerUpdated.connect(
      mem_fun(*this, &Reflector::onTalkerUpdated));
  TGHandler::instance()->requestAutoQsy.connect(
      mem_fun(*this, &Reflector::onRequestAutoQsy));
  m_renew_cert_timer.expired.connect(
      [&](Async::AtTimer*)
      {
        if (!loadServerCertificateFiles())
        {
          std::cerr << "*** WARNING: Failed to renew server certificate"
                    << std::endl;
        }
      });
  m_renew_issue_ca_cert_timer.expired.connect(
      [&](Async::AtTimer*)
      {
        if (!loadSigningCAFiles())
        {
          std::cerr << "*** WARNING: Failed to renew issuing CA certificate"
                    << std::endl;
        }
      });
  m_status["nodes"] = Json::Value(Json::objectValue);
} /* Reflector::Reflector */


Reflector::~Reflector(void)
{
  delete m_http_server;
  m_http_server = 0;
  delete m_udp_sock;
  m_udp_sock = 0;
  delete m_srv;
  m_srv = 0;
  delete m_cmd_pty;
  m_cmd_pty = 0;
  m_client_con_map.clear();
  ReflectorClient::cleanup();
  delete TGHandler::instance();
} /* Reflector::~Reflector */


bool Reflector::initialize(Async::Config &cfg)
{
  m_cfg = &cfg;
  TGHandler::instance()->setConfig(m_cfg);

  std::string listen_port("5300");
  cfg.getValue("GLOBAL", "LISTEN_PORT", listen_port);
  m_srv = new TcpServer<FramedTcpConnection>(listen_port);
  m_srv->setConnectionThrottling(10, 0.1, 1000);
  m_srv->clientConnected.connect(
      mem_fun(*this, &Reflector::clientConnected));
  m_srv->clientDisconnected.connect(
      mem_fun(*this, &Reflector::clientDisconnected));

  if (!loadCertificateFiles())
  {
    return false;
  }

  m_srv->setSslContext(m_ssl_ctx);

  uint16_t udp_listen_port = 5300;
  cfg.getValue("GLOBAL", "LISTEN_PORT", udp_listen_port);
  m_udp_sock = new Async::EncryptedUdpSocket(udp_listen_port);
  const char* err = "unknown reason";
  if ((err="bad allocation",          (m_udp_sock == 0)) ||
      (err="initialization failure",  !m_udp_sock->initOk()) ||
      (err="unsupported cipher",      !m_udp_sock->setCipher(UdpCipher::NAME)))
  {
    std::cerr << "*** ERROR: Could not initialize UDP socket due to "
              << err << std::endl;
    return false;
  }
  m_udp_sock->setCipherAADLength(UdpCipher::AADLEN);
  m_udp_sock->setTagLength(UdpCipher::TAGLEN);
  m_udp_sock->cipherDataReceived.connect(
      mem_fun(*this, &Reflector::udpCipherDataReceived));
  m_udp_sock->dataReceived.connect(
      mem_fun(*this, &Reflector::udpDatagramReceived));

  unsigned sql_timeout = 0;
  cfg.getValue("GLOBAL", "SQL_TIMEOUT", sql_timeout);
  TGHandler::instance()->setSqlTimeout(sql_timeout);

  unsigned sql_timeout_blocktime = 60;
  cfg.getValue("GLOBAL", "SQL_TIMEOUT_BLOCKTIME", sql_timeout_blocktime);
  TGHandler::instance()->setSqlTimeoutBlocktime(sql_timeout_blocktime);

  m_cfg->getValue("GLOBAL", "TG_FOR_V1_CLIENTS", m_tg_for_v1_clients);

  SvxLink::SepPair<uint32_t, uint32_t> random_qsy_range;
  if (m_cfg->getValue("GLOBAL", "RANDOM_QSY_RANGE", random_qsy_range))
  {
    m_random_qsy_lo = random_qsy_range.first;
    m_random_qsy_hi = m_random_qsy_lo + random_qsy_range.second-1;
    if ((m_random_qsy_lo < 1) || (m_random_qsy_hi < m_random_qsy_lo))
    {
      cout << "*** WARNING: Illegal RANDOM_QSY_RANGE specified. Ignored."
           << endl;
      m_random_qsy_hi = m_random_qsy_lo = 0;
    }
    m_random_qsy_tg = m_random_qsy_hi;
  }

  std::string http_srv_port;
  if (m_cfg->getValue("GLOBAL", "HTTP_SRV_PORT", http_srv_port))
  {
    m_http_server = new Async::TcpServer<Async::HttpServerConnection>(http_srv_port);
    m_http_server->clientConnected.connect(
        sigc::mem_fun(*this, &Reflector::httpClientConnected));
    m_http_server->clientDisconnected.connect(
        sigc::mem_fun(*this, &Reflector::httpClientDisconnected));
  }

  // Path for command PTY
  string pty_path;
  m_cfg->getValue("GLOBAL", "COMMAND_PTY", pty_path);
  if (!pty_path.empty())
  {
    m_cmd_pty = new Pty(pty_path);
    if ((m_cmd_pty == nullptr) || !m_cmd_pty->open())
    {
      std::cerr << "*** ERROR: Could not open command PTY '" << pty_path
                << "' as specified in configuration variable "
                   "GLOBAL/COMMAND_PTY" << std::endl;
      return false;
    }
    m_cmd_pty->setLineBuffered(true);
    m_cmd_pty->dataReceived.connect(
        mem_fun(*this, &Reflector::ctrlPtyDataReceived));
  }

  m_cfg->getValue("GLOBAL", "ACCEPT_CERT_EMAIL", m_accept_cert_email);

  m_cfg->valueUpdated.connect(sigc::mem_fun(*this, &Reflector::cfgUpdated));

  // >>>>> Userlisten initial einlesen
  (void)reloadAllUserLists(*m_cfg);

  // >>>>> QSY-Deny-Liste initial laden
  g_qsy_deny_file = "/etc/svxlink/svxreflector.d/qsy_deny.conf";
  (void)m_cfg->getValue("GLOBAL", "QSY_DENY_FILE", g_qsy_deny_file);
  (void)loadQsyDenyList(g_qsy_deny_file);

  // >>>>> TG-Handling-Datei initial laden
  g_tg_handling_file = "/etc/svxlink/svxreflector.d/tg_handling.conf";
  (void)m_cfg->getValue("GLOBAL", "TG_HANDLING_FILE", g_tg_handling_file);
  (void)loadTgHandlingFile(*m_cfg, g_tg_handling_file);

  return true;
} /* Reflector::initialize */


void Reflector::nodeList(std::vector<std::string>& nodes) const
{
  nodes.clear();
  for (const auto& item : m_client_con_map)
  {
    const std::string& callsign = item.second->callsign();
    if (!callsign.empty())
    {
      nodes.push_back(callsign);
    }
  }
} /* Reflector::nodeList */


void Reflector::broadcastMsg(const ReflectorMsg& msg,
                             const ReflectorClient::Filter& filter)
{
  for (const auto& item : m_client_con_map)
  {
    ReflectorClient *client = item.second;
    if (filter(client) &&
        (client->conState() == ReflectorClient::STATE_CONNECTED))
    {
      client->sendMsg(msg);
    }
  }
} /* Reflector::broadcastMsg */


bool Reflector::sendUdpDatagram(ReflectorClient *client,
    const ReflectorUdpMsg& msg)
{
  auto udp_addr = client->remoteUdpHost();
  auto udp_port = client->remoteUdpPort();
  if (client->protoVer() >= ProtoVer(3, 0))
  {
    ReflectorUdpMsg header(msg.type());
    ostringstream ss;
    assert(header.pack(ss) && msg.pack(ss));

    m_udp_sock->setCipherIV(client->udpCipherIV());
    m_udp_sock->setCipherKey(client->udpCipherKey());
    UdpCipher::AAD aad{client->udpCipherIVCntrNext()};
    std::stringstream aadss;
    if (!aad.pack(aadss))
    {
      std::cout << "*** WARNING: Packing associated data failed for UDP "
                   "datagram to " << udp_addr << ":" << udp_port << std::endl;
      return false;
    }
    return m_udp_sock->write(udp_addr, udp_port,
                             aadss.str().data(), aadss.str().size(),
                             ss.str().data(), ss.str().size());
  }
  else
  {
    ReflectorUdpMsgV2 header(msg.type(), client->clientId(),
        client->udpCipherIVCntrNext() & 0xffff);
    ostringstream ss;
    assert(header.pack(ss) && msg.pack(ss));
    return m_udp_sock->UdpSocket::write(
        udp_addr, udp_port,
        ss.str().data(), ss.str().size());
  }
} /* Reflector::sendUdpDatagram */


void Reflector::broadcastUdpMsg(const ReflectorUdpMsg& msg,
                                const ReflectorClient::Filter& filter)
{
  for (const auto& item : m_client_con_map)
  {
    ReflectorClient *client = item.second;
    if (filter(client) &&
        (client->conState() == ReflectorClient::STATE_CONNECTED))
    {
      client->sendUdpMsg(msg);
    }
  }
} /* Reflector::broadcastUdpMsg */


void Reflector::requestQsy(ReflectorClient *client, uint32_t tg)
{
  uint32_t current_tg = TGHandler::instance()->TGForClient(client);
  if (current_tg == 0)
  {
    std::cout << client->callsign()
              << ": Cannot request QSY from TG #0" << std::endl;
    return;
  }

  // QSY-Deny prüfen
  if (!qsyAllowedForClient(client)) {
    return;
  }

  if (tg == 0)
  {
    tg = nextRandomQsyTg();
    if (tg == 0) { return; }
  }

  cout << client->callsign() << ": Requesting QSY from TG #"
       << current_tg << " to TG #" << tg << endl;

  broadcastMsg(MsgRequestQsy(tg),
      ReflectorClient::mkAndFilter(
        ge_v2_client_filter,
        ReflectorClient::TgFilter(current_tg)));
} /* Reflector::requestQsy */


Async::SslCertSigningReq
Reflector::loadClientPendingCsr(const std::string& callsign)
{
  Async::SslCertSigningReq csr;
  (void)csr.readPemFile(m_pending_csrs_dir + "/" + callsign + ".csr");
  return csr;
} /* Reflector::loadClientPendingCsr */


Async::SslCertSigningReq
Reflector::loadClientCsr(const std::string& callsign)
{
  Async::SslCertSigningReq csr;
  (void)csr.readPemFile(m_csrs_dir + "/" + callsign + ".csr");
  return csr;
} /* Reflector::loadClientPendingCsr */


bool Reflector::renewedClientCert(Async::SslX509& cert)
{
  if (cert.isNull())
  {
    return false;
  }

  std::string callsign(cert.commonName());
  Async::SslX509 new_cert = loadClientCertificate(callsign);
  if (!new_cert.isNull() &&
      ((new_cert.publicKey() != cert.publicKey()) ||
       (timeToRenewCert(new_cert) <= std::time(NULL))))
  {
    return signClientCert(cert, "CRT_RENEWED");
  }
  cert = std::move(new_cert);
  return !cert.isNull();
} /* Reflector::renewedClientCert */


bool Reflector::signClientCert(Async::SslX509& cert, const std::string& ca_op)
{
  cert.setSerialNumber();
  cert.setIssuerName(m_issue_ca_cert.subjectName());
  cert.setValidityTime(CERT_VALIDITY_DAYS, CERT_VALIDITY_OFFSET_DAYS);
  auto cn = cert.commonName();
  if (!cert.sign(m_issue_ca_pkey))
  {
    std::cerr << "*** ERROR: Certificate signing failed for client "
              << cn << std::endl;
    return false;
  }
  auto crtfile = m_certs_dir + "/" + cn + ".crt";
  if (cert.writePemFile(crtfile) && m_issue_ca_cert.appendPemFile(crtfile))
  {
    runCAHook({
        { "CA_OP",      ca_op },
        { "CA_CRT_PEM", cert.pem() }
      });
  }
  else
  {
    std::cerr << "*** WARNING: Failed to write client certificate file '"
              << crtfile << "'" << std::endl;
  }
  return true;
} /* Reflector::signClientCert */


Async::SslX509 Reflector::signClientCsr(const std::string& cn)
{
  Async::SslX509 cert(nullptr);

  Async::SslCertSigningReq req = loadClientPendingCsr(cn);
  if (req.isNull())
  {
    std::cerr << "*** ERROR: Cannot find CSR to sign '" << req.filePath()
              << "'" << std::endl;
    return cert;
  }

  cert.clear();
  cert.setVersion(Async::SslX509::VERSION_3);
  cert.setSubjectName(req.subjectName());
  const Async::SslX509Extensions exts(req.extensions());
  Async::SslX509Extensions cert_exts;
  cert_exts.addBasicConstraints("critical, CA:FALSE");
  cert_exts.addKeyUsage(
      "critical, digitalSignature, keyEncipherment, keyAgreement");
  cert_exts.addExtKeyUsage("clientAuth");
  Async::SslX509ExtSubjectAltName san(exts.subjectAltName());
  cert_exts.addExtension(san);
  Async::SslKeypair csr_pkey(req.publicKey());
  cert.setPublicKey(csr_pkey);

  if (!signClientCert(cert, "CSR_SIGNED"))
  {
    cert.set(nullptr);
  }

  std::string csr_path = m_csrs_dir + "/" + cn + ".csr";
  if (rename(req.filePath().c_str(), csr_path.c_str()) != 0)
  {
    auto errstr = SvxLink::strError(errno);
    std::cerr << "*** WARNING: Failed to move signed CSR from '"
              << req.filePath() << "' to '" << csr_path << "': "
              << errstr << std::endl;
  }

  auto client = ReflectorClient::lookup(cn);
  if ((client != nullptr) && !cert.isNull())
  {
    client->certificateUpdated(cert);
  }

  return cert;
} /* Reflector::signClientCsr */


Async::SslX509 Reflector::loadClientCertificate(const std::string& callsign)
{
  Async::SslX509 cert;
  if (!cert.readPemFile(m_certs_dir + "/" + callsign + ".crt") ||
      cert.isNull() ||
      !cert.timeIsWithinRange())
  {
    return nullptr;
  }
  return cert;
} /* Reflector::loadClientCertificate */


std::string Reflector::clientCertPem(const std::string& callsign) const
{
  std::string crtfile(m_certs_dir + "/" + callsign + ".crt");
  std::ifstream ifs(crtfile);
  if (!ifs.good())
  {
    return std::string();
  }
  return std::string(std::istreambuf_iterator<char>{ifs}, {});
} /* Reflector::clientCertPem */


std::string Reflector::caBundlePem(void) const
{
  std::ifstream ifs(m_ca_bundle_file);
  if (ifs.good())
  {
    return std::string(std::istreambuf_iterator<char>{ifs}, {});
  }
  return std::string();
} /* Reflector::caBundlePem */


std::string Reflector::issuingCertPem(void) const
{
  return m_issue_ca_cert.pem();
} /* Reflector::issuingCertPem */


bool Reflector::callsignOk(const std::string& callsign) const
{
  if (callsign.empty())
  {
    std::cout << "*** WARNING: The callsign is empty" << std::endl;
    return false;
  }

  std::string accept_cs_re_str;
  if (!m_cfg->getValue("GLOBAL", "ACCEPT_CALLSIGN", accept_cs_re_str) ||
      accept_cs_re_str.empty())
  {
    accept_cs_re_str =
      "[A-Z0-9][A-Z]{0,2}\\d[A-Z0-9]{0,3}[A-Z](?:-[A-Z0-9]{1,3})?";
  }
  const std::regex accept_callsign_re(accept_cs_re_str);
  if (!std::regex_match(callsign, accept_callsign_re))
  {
    std::cerr << "*** WARNING: The callsign '" << callsign
              << "' is not accepted by configuration (ACCEPT_CALLSIGN)"
              << std::endl;
    return false;
  }

  std::string reject_cs_re_str;
  m_cfg->getValue("GLOBAL", "REJECT_CALLSIGN", reject_cs_re_str);
  if (!reject_cs_re_str.empty())
  {
    const std::regex reject_callsign_re(reject_cs_re_str);
    if (std::regex_match(callsign, reject_callsign_re))
    {
      std::cerr << "*** WARNING: The callsign '" << callsign
                << "' has been rejected by configuration (REJECT_CALLSIGN)."
                << std::endl;
      return false;
    }
  }

  return true;
} /* Reflector::callsignOk */


bool Reflector::emailOk(const std::string& email) const
{
  if (m_accept_cert_email.empty())
  {
    return true;
  }
  return std::regex_match(email, std::regex(m_accept_cert_email));
} /* Reflector::emailOk */


bool Reflector::reqEmailOk(const Async::SslCertSigningReq& req) const
{
  if (req.isNull())
  {
    return false;
  }

  const auto san = req.extensions().subjectAltName();
  if (san.isNull())
  {
    return emailOk("");
  }

  size_t email_cnt = 0;
  bool email_ok = true;
  san.forEach(
      [&](int type, std::string value)
      {
        email_cnt += 1;
        email_ok &= emailOk(value);
      },
      GEN_EMAIL);
  email_ok &= (email_cnt > 0) || emailOk("");
  return email_ok;
} /* Reflector::reqEmailOk */


std::string Reflector::checkCsr(const Async::SslCertSigningReq& req)
{
  if (!callsignOk(req.commonName()))
  {
    return std::string("Certificate signing request with invalid callsign '") +
           req.commonName() + "'";
  }
  if (!reqEmailOk(req))
  {
    return std::string(
             "Certificate signing request with no or invalid CERT_EMAIL"
           );
  }
  return "";
} /* Reflector::checkCsr */


Async::SslX509 Reflector::csrReceived(Async::SslCertSigningReq& req)
{
  if (req.isNull())
  {
    return nullptr;
  }

  std::string callsign(req.commonName());
  if (!callsignOk(callsign))
  {
    std::cerr << "*** WARNING: The CSR CN (callsign) check failed"
              << std::endl;
    return nullptr;
  }

  std::string csr_path(m_csrs_dir + "/" + callsign + ".csr");
  Async::SslCertSigningReq csr;
  if (!csr.readPemFile(csr_path))
  {
    csr.set(nullptr);
  }

  if (!csr.isNull() && (req.publicKey() != csr.publicKey()))
  {
    std::cerr << "*** WARNING: The received CSR with callsign '"
              << callsign << "' has a different public key "
                 "than the current CSR. That may be a sign of someone "
                 "trying to hijack a callsign or the owner of the "
                 "callsign has generated a new private/public key pair."
              << std::endl;
    return nullptr;
  }

  Async::SslX509 cert = loadClientCertificate(callsign);
  if (!cert.isNull() &&
      ((cert.publicKey() != req.publicKey()) ||
       (timeToRenewCert(cert) <= std::time(NULL))))
  {
    cert.set(nullptr);
  }

  const std::string pending_csr_path(
      m_pending_csrs_dir + "/" + callsign + ".csr");
  Async::SslCertSigningReq pending_csr;
  if ((
        csr.isNull() ||
        (req.digest() != csr.digest()) ||
        cert.isNull()
      ) && (
        !pending_csr.readPemFile(pending_csr_path) ||
        (req.digest() != pending_csr.digest())
      ))
  {
    std::cout << callsign << ": Add pending CSR '" << pending_csr_path
              << "' to CA" << std::endl;
    if (req.writePemFile(pending_csr_path))
    {
      const auto ca_op =
        pending_csr.isNull() ? "PENDING_CSR_CREATE" : "PENDING_CSR_UPDATE";
      runCAHook({
          { "CA_OP",      ca_op },
          { "CA_CSR_PEM", req.pem() }
        });
    }
    else
    {
      std::cerr << "*** WARNING: Could not write CSR file '"
                << pending_csr_path << "'" << std::endl;
    }
  }

  return cert;
} /* Reflector::csrReceived */


Json::Value& Reflector::clientStatus(const std::string& callsign)
{
  if (!m_status.isMember(callsign))
  {
    m_status["nodes"][callsign] = Json::Value(Json::objectValue);
  }
  return m_status["nodes"][callsign];
} /* Reflector::clientStatus */


/****************************************************************************
 *
 * Protected member functions
 *
 ****************************************************************************/



/****************************************************************************
 *
 * Private member functions
 *
 ****************************************************************************/

void Reflector::clientConnected(Async::FramedTcpConnection *con)
{
  std::cout << con->remoteHost() << ":" << con->remotePort()
       << ": Client connected" << endl;
  ReflectorClient *client = new ReflectorClient(this, con, m_cfg);
  con->verifyPeer.connect(sigc::mem_fun(*this, &Reflector::onVerifyPeer));
  m_client_con_map[con] = client;
} /* Reflector::clientConnected */


void Reflector::clientDisconnected(Async::FramedTcpConnection *con,
                           Async::FramedTcpConnection::DisconnectReason reason)
{
  ReflectorClientConMap::iterator it = m_client_con_map.find(con);
  assert(it != m_client_con_map.end());
  ReflectorClient *client = (*it).second;

  TGHandler::instance()->removeClient(client);

  if (!client->callsign().empty())
  {
    cout << client->callsign() << ": ";
  }
  else
  {
    std::cout << con->remoteHost() << ":" << con->remotePort() << ": ";
  }
  std::cout << "Client disconnected: "
            << TcpConnection::disconnectReasonStr(reason) << std::endl;

  m_client_con_map.erase(it);

  if (!client->callsign().empty())
  {
    m_status["nodes"].removeMember(client->callsign());
    broadcastMsg(MsgNodeLeft(client->callsign()),
        ReflectorClient::ExceptFilter(client));
  }
  delete client;
} /* Reflector::clientDisconnected */


bool Reflector::udpCipherDataReceived(const IpAddress& addr, uint16_t port,
                                      void *buf, int count)
{
  if ((count <= 0) || (static_cast<size_t>(count) < UdpCipher::AADLEN))
  {
    std::cout << "### : Ignoring too short UDP datagram (" << count
              << " bytes)" << std::endl;
    return true;
  }

  stringstream ss;
  ss.write(reinterpret_cast<const char *>(buf), UdpCipher::AADLEN);
  assert(m_aad.unpack(ss));

  ReflectorClient* client = nullptr;
  if (m_aad.iv_cntr == 0)
  {
    UdpCipher::InitialAAD iaad;
    if (static_cast<size_t>(count) < iaad.packedSize())
    {
      std::cout << "### Reflector::udpCipherDataReceived: "
                   "Ignoring malformed UDP registration datagram" << std::endl;
      return true;
    }
    ss.clear();
    ss.write(reinterpret_cast<const char *>(buf)+UdpCipher::AADLEN,
        sizeof(UdpCipher::ClientId));

    Async::MsgPacker<UdpCipher::ClientId>::unpack(ss, iaad.client_id);
    auto client = ReflectorClient::lookup(iaad.client_id);
    if (client == nullptr)
    {
      std::cout << "### Could not find client id (" << iaad.client_id
                << ") specified in initial AAD datagram" << std::endl;
      return true;
    }
    m_udp_sock->setCipherIV(UdpCipher::IV{client->udpCipherIVRand(),
                                          client->clientId(), 0});
    m_udp_sock->setCipherKey(client->udpCipherKey());
    m_udp_sock->setCipherAADLength(iaad.packedSize());
  }
  else if ((client=ReflectorClient::lookup(std::make_pair(addr, port))))
  {
    m_udp_sock->setCipherIV(UdpCipher::IV{client->udpCipherIVRand(),
                                          client->clientId(), m_aad.iv_cntr});
    m_udp_sock->setCipherKey(client->udpCipherKey());
    m_udp_sock->setCipherAADLength(UdpCipher::AADLEN);
  }
  else
  {
    udpDatagramReceived(addr, port, nullptr, buf, count);
    return true;
  }

  return false;
} /* Reflector::udpCipherDataReceived */


void Reflector::udpDatagramReceived(const IpAddress& addr, uint16_t port,
                                    void* aadptr, void *buf, int count)
{
  assert(m_udp_sock->cipherAADLength() >= UdpCipher::AADLEN);

  stringstream ss;
  ss.write(reinterpret_cast<const char *>(buf), static_cast<size_t>(count));

  ReflectorUdpMsg header;
  if (!header.unpack(ss))
  {
    cout << "*** WARNING: Unpacking message header failed for UDP datagram "
            "from " << addr << ":" << port << endl;
    return;
  }
  ReflectorUdpMsgV2 header_v2;

  ReflectorClient* client = nullptr;
  UdpCipher::AAD aad;
  if (aadptr != nullptr)
  {
    stringstream aadss;
    aadss.write(reinterpret_cast<const char *>(aadptr),
        m_udp_sock->cipherAADLength());

    if (!aad.unpack(aadss))
    {
      return;
    }
    if (aad.iv_cntr == 0) // Client UDP registration
    {
      UdpCipher::InitialAAD iaad;
      assert(aadss.seekg(0));
      if (!iaad.unpack(aadss))
      {
        std::cout << "### Reflector::udpDatagramReceived: "
                     "Could not unpack iaad" << std::endl;
        return;
      }
      assert(iaad.iv_cntr == 0);
      client = ReflectorClient::lookup(iaad.client_id);
      if (client == nullptr)
      {
        std::cout << "### Reflector::udpDatagramReceived: Could not find "
                     "client id " << iaad.client_id << std::endl;
        return;
      }
      else if (client->remoteUdpPort() == 0)
      {
        //client->setRemoteUdpPort(port);
      }
      else
      {
        std::cout << "### Reflector::udpDatagramReceived: Client "
                  << iaad.client_id << " already registered." << std::endl;
      }
      client->setUdpRxSeq(0);
    }
    else
    {
      client = ReflectorClient::lookup(std::make_pair(addr, port));
      if (client == nullptr)
      {
        std::cout << "### Unknown client " << addr << ":" << port << std::endl;
        return;
      }
    }
  }
  else
  {
    ss.seekg(0);
    if (!header_v2.unpack(ss))
    {
      std::cout << "*** WARNING: Unpacking V2 message header failed for UDP "
              "datagram from " << addr << ":" << port << std::endl;
      return;
    }
    client = ReflectorClient::lookup(header_v2.clientId());
    if (client == nullptr)
    {
      std::cerr << "*** WARNING: Incoming V2 UDP datagram from " << addr << ":"
           << port << " has invalid client id " << header_v2.clientId()
           << std::endl;
      return;
    }

  }

  if (client && !client->callsign().empty())
  {
    applyBlockForCallsign(client->callsign());
  }

  if (client->remoteUdpPort() == 0)
  {
    client->setRemoteUdpSource(std::make_pair(addr, port));
    client->sendUdpMsg(MsgUdpHeartbeat());
  }
  if (port != client->remoteUdpPort())
  {
    cerr << "*** WARNING[" << client->callsign()
         << "]: Incoming UDP packet has the wrong source UDP "
            "port number, " << port << " instead of "
         << client->remoteUdpPort() << endl;
    return;
  }

  if (client->protoVer() >= ProtoVer(3, 0))
  {
    if (aad.iv_cntr < client->nextUdpRxSeq())
    {
      std::cout << client->callsign()
                << ": Dropping out of sequence UDP frame with seq="
                << aad.iv_cntr << std::endl;
      return;
    }
    else if (aad.iv_cntr > client->nextUdpRxSeq())
    {
      std::cout << client->callsign() << ": UDP frame(s) lost. Expected seq="
                << client->nextUdpRxSeq()
                << " but received " << aad.iv_cntr
                << ". Resetting next expected sequence number to "
                << (aad.iv_cntr + 1) << std::endl;
    }
    client->setUdpRxSeq(aad.iv_cntr + 1);
  }
  else
  {
    uint16_t next_udp_rx_seq = client->nextUdpRxSeq() & 0xffff;
    uint16_t udp_rx_seq_diff = header_v2.sequenceNum() - next_udp_rx_seq;
    if (udp_rx_seq_diff > 0x7fff)
    {
      std::cout << client->callsign()
                << ": Dropping out of sequence frame with seq="
                << header_v2.sequenceNum() << ". Expected seq="
                << next_udp_rx_seq << std::endl;
      return;
    }
    else if (udp_rx_seq_diff > 0)
    {
      cout << client->callsign()
           << ": UDP frame(s) lost. Expected seq=" << next_udp_rx_seq
           << ". Received seq=" << header_v2.sequenceNum() << endl;
    }
    client->setUdpRxSeq(header_v2.sequenceNum() + 1);
  }

  client->udpMsgReceived(header);

  switch (header.type())
  {
    case MsgUdpHeartbeat::TYPE:
      break;

    case MsgUdpAudio::TYPE:
    {
      if (!client->isBlocked())
      {
        MsgUdpAudio msg;
        if (!msg.unpack(ss))
        {
          cerr << "*** WARNING[" << client->callsign()
               << "]: Could not unpack incoming MsgUdpAudioV1 message" << endl;
          return;
        }
        uint32_t tg = TGHandler::instance()->TGForClient(client);
        if (!msg.audioData().empty() && (tg > 0))
        {
          ReflectorClient* talker = TGHandler::instance()->talkerForTG(tg);
          if (talker == 0)
          {
            TGHandler::instance()->setTalkerForTG(tg, client);
            talker = TGHandler::instance()->talkerForTG(tg);
          }
          if (talker == client)
          {
            TGHandler::instance()->setTalkerForTG(tg, client);
            broadcastUdpMsg(msg,
                ReflectorClient::mkAndFilter(
                  ReflectorClient::ExceptFilter(client),
                  ReflectorClient::TgFilter(tg)));
          }
        }
      }
      break;
    }

    case MsgUdpFlushSamples::TYPE:
    {
      uint32_t tg = TGHandler::instance()->TGForClient(client);
      ReflectorClient* talker = TGHandler::instance()->talkerForTG(tg);
      if ((tg > 0) && (client == talker))
      {
        TGHandler::instance()->setTalkerForTG(tg, 0);
      }
      client->sendUdpMsg(MsgUdpAllSamplesFlushed());
      break;
    }

    case MsgUdpAllSamplesFlushed::TYPE:
      break;

    case MsgUdpSignalStrengthValues::TYPE:
    {
      if (!client->isBlocked())
      {
        MsgUdpSignalStrengthValues msg;
        if (!msg.unpack(ss))
        {
          cerr << "*** WARNING[" << client->callsign()
               << "]: Could not unpack incoming "
                  "MsgUdpSignalStrengthValues message" << endl;
          return;
        }
        typedef MsgUdpSignalStrengthValues::Rxs::const_iterator RxsIter;
        for (RxsIter it = msg.rxs().begin(); it != msg.rxs().end(); ++it)
        {
          const MsgUdpSignalStrengthValues::Rx& rx = *it;
          client->setRxSiglev(rx.id(), rx.siglev());
          client->setRxEnabled(rx.id(), rx.enabled());
          client->setRxSqlOpen(rx.id(), rx.sqlOpen());
          client->setRxActive(rx.id(), rx.active());
        }
      }
      break;
    }

    default:
      break;
  }
} /* Reflector::udpDatagramReceived */


void Reflector::onTalkerUpdated(uint32_t tg, ReflectorClient* old_talker,
                                ReflectorClient *new_talker)
{
  if (old_talker != 0)
  {
    cout << old_talker->callsign() << ": Talker stop on TG #" << tg << endl;
    old_talker->updateIsTalker();
    broadcastMsg(MsgTalkerStop(tg, old_talker->callsign()),
        ReflectorClient::mkAndFilter(
          ge_v2_client_filter,
          ReflectorClient::mkOrFilter(
            ReflectorClient::TgFilter(tg),
            ReflectorClient::TgMonitorFilter(tg))));
    if (tg == tgForV1Clients())
    {
      broadcastMsg(MsgTalkerStopV1(old_talker->callsign()), v1_client_filter);
    }
    broadcastUdpMsg(MsgUdpFlushSamples(),
          ReflectorClient::mkAndFilter(
            ReflectorClient::TgFilter(tg),
            ReflectorClient::ExceptFilter(old_talker)));
  }
  if (new_talker != 0)
  {
    cout << new_talker->callsign() << ": Talker start on TG #" << tg << endl;
    new_talker->updateIsTalker();
    broadcastMsg(MsgTalkerStart(tg, new_talker->callsign()),
        ReflectorClient::mkAndFilter(
          ge_v2_client_filter,
          ReflectorClient::mkOrFilter(
            ReflectorClient::TgFilter(tg),
            ReflectorClient::TgMonitorFilter(tg))));
    if (tg == tgForV1Clients())
    {
      broadcastMsg(MsgTalkerStartV1(new_talker->callsign()), v1_client_filter);
    }
  }
} /* Reflector::onTalkerUpdated */


void Reflector::httpRequestReceived(Async::HttpServerConnection *con,
                                    Async::HttpServerConnection::Request& req)
{
  Async::HttpServerConnection::Response res;
  if ((req.method != "GET") && (req.method != "HEAD"))
  {
    res.setCode(501);
    res.setContent("application/json",
        "{\"msg\":\"" + req.method + ": Method not implemented\"}");
    con->write(res);
    return;
  }

  if (req.target != "/status")
  {
    res.setCode(404);
    res.setContent("application/json",
        "{\"msg\":\"Not found!\"}");
    con->write(res);
    return;
  }

  std::ostringstream os;
  Json::StreamWriterBuilder builder;
  builder["commentStyle"] = "None";
  builder["indentation"] = "";
  Json::StreamWriter* writer = builder.newStreamWriter();
  writer->write(m_status, &os);
  delete writer;

  res.setContent("application/json", os.str());
  res.setSendContent(req.method == "GET");
  res.setCode(200);
  con->write(res);
} /* Reflector::requestReceived */


void Reflector::httpClientConnected(Async::HttpServerConnection *con)
{
  con->requestReceived.connect(sigc::mem_fun(*this, &Reflector::httpRequestReceived));
} /* Reflector::httpClientConnected */


void Reflector::httpClientDisconnected(Async::HttpServerConnection *con,
    Async::HttpServerConnection::DisconnectReason reason)
{
} /* Reflector::httpClientDisconnected */


void Reflector::onRequestAutoQsy(uint32_t from_tg)
{
  // Herausfinden, wer das QSY angefordert hat (Talker)
  ReflectorClient* talker = TGHandler::instance()->talkerForTG(from_tg);
  if (talker && !qsyAllowedForClient(talker)) {
    return;
  }

  uint32_t tg = nextRandomQsyTg();
  if (tg == 0) { return; }

  std::cout << "Requesting auto-QSY from TG #" << from_tg
            << " to TG #" << tg << std::endl;

  broadcastMsg(MsgRequestQsy(tg),
      ReflectorClient::mkAndFilter(
        ge_v2_client_filter,
        ReflectorClient::TgFilter(from_tg)));
} /* Reflector::onRequestAutoQsy */


uint32_t Reflector::nextRandomQsyTg(void)
{
  if (m_random_qsy_tg == 0)
  {
    std::cout << "*** WARNING: QSY request for random TG "
              << "requested but RANDOM_QSY_RANGE is empty" << std::endl;
    return 0;
  }

  assert (m_random_qsy_tg != 0);
  uint32_t range_size = m_random_qsy_hi-m_random_qsy_lo+1;
  uint32_t i;
  for (i=0; i<range_size; ++i)
  {
    m_random_qsy_tg = (m_random_qsy_tg < m_random_qsy_hi) ?
      m_random_qsy_tg+1 : m_random_qsy_lo;
    if (TGHandler::instance()->clientsForTG(m_random_qsy_tg).empty())
    {
      return m_random_qsy_tg;
    }
  }

  std::cout << "*** WARNING: No random TG available for QSY" << std::endl;
  return 0;
} /* Reflector::nextRandomQsyTg */


void Reflector::ctrlPtyDataReceived(const void *buf, size_t count)
{
  const char* ptr = reinterpret_cast<const char*>(buf);
  const std::string cmdline(ptr, ptr + count);
  std::istringstream ss(cmdline);
  std::ostringstream errss;
  std::string cmd;
  if (!(ss >> cmd))
  {
    errss << "Invalid PTY command '" << cmdline << "'";
    goto write_status;
  }
  std::transform(cmd.begin(), cmd.end(), cmd.begin(), ::toupper);

  if (cmd == "CFG")
  {
    std::string section, tag, value;
    ss >> section >> tag >> value;
    if (!value.empty())
    {
      m_cfg->setValue(section, tag, value);
    }
    else if (!tag.empty())
    {
      std::cout << section << "/" << tag << "=\""
                << m_cfg->getValue(section, tag) << "\""
                << std::endl;
    }
    else if (!section.empty())
    {
      for (const auto& tag : m_cfg->listSection(section))
      {
        std::cout << section << "/" << tag << "=\""
                  << m_cfg->getValue(section, tag) << "\""
                  << std::endl;
      }
    }
    else
    {
      for (const auto& section : m_cfg->listSections())
      {
        for (const auto& tag : m_cfg->listSection(section))
        {
          std::cout << section << "/" << tag << "=\""
                    << m_cfg->getValue(section, tag) << "\""
                    << std::endl;
        }
      }
    }
  }
  else if (cmd == "NODE")
  {
    std::string subcmd, callsign, blocktime_str;
    if (!(ss >> subcmd >> callsign >> blocktime_str))
    {
      errss << "Invalid NODE PTY command '" << cmdline << "'. "
               "Usage: NODE BLOCK <callsign> <seconds|0|00>";
      goto write_status;
    }
    std::transform(subcmd.begin(), subcmd.end(), subcmd.begin(), ::toupper);

    if (subcmd == "UNBLOCK") { blocktime_str = "0"; subcmd = "BLOCK"; }

    if (subcmd == "BLOCK")
    {
      ReflectorClient* node = ReflectorClient::lookup(callsign);

      const bool permanent = (blocktime_str == "00");
      unsigned blocktime_val = 0;

      if (!permanent)
      {
        try
        {
          size_t idx = 0;
          unsigned long v = std::stoul(blocktime_str, &idx, 10);
          if (idx != blocktime_str.size())
            throw std::invalid_argument("trailing chars");
          blocktime_val = static_cast<unsigned>(v);
        }
        catch (const std::exception&)
        {
          errss << "Invalid blocktime '" << blocktime_str
                << "'. Use <seconds|0|00>";
          goto write_status;
        }
      }

      if (permanent)
      {
        g_blocked_until_epoch[callsign] = std::numeric_limits<uint64_t>::max();
        (void)saveBlockedList();

        std::cout << callsign << ": Unblock state changed -> PERMANENT BLOCK" << std::endl;

        if (node)
        {
          node->setBlock(ReflectorClient::PERM_BLOCKTIME);
          node->sendMsg(MsgError("You are permanently blocked for some reason - please contact Admin Team!"));
        }
      }
      else if (blocktime_val == 0)
      {
        g_blocked_until_epoch.erase(callsign);
        (void)saveBlockedList();

        std::cout << callsign << ": Unblocked" << std::endl;

        if (node)
        {
          node->setBlock(0);
          node->sendMsg(MsgError("You are unblocked."));
        }
        else
        {
          g_unblock_notice_until[callsign] = nowEpoch() + 3600;
        }
      }
      else
      {
        const uint64_t until = nowEpoch() + static_cast<uint64_t>(blocktime_val);
        g_blocked_until_epoch[callsign] = until;
        (void)saveBlockedList();

        std::cout << callsign << ": Temporary block for "
                  << blocktime_val << " seconds" << std::endl;

        if (node)
        {
          node->setBlock(blocktime_val);
          node->sendMsg(MsgError(std::string("You are blocked for ")
                                 + std::to_string(blocktime_val) + " seconds for some reason - please contact Admin Team!"));
        }
      }
    }
    else
    {
      errss << "Invalid NODE PTY command '" << cmdline << "'. "
               "Usage: NODE BLOCK <callsign> <seconds|0|00>";
      goto write_status;
    }
  }
  else if (cmd == "USERLIST")
  {
    std::string subcmd;
    if (!(ss >> subcmd)) {
      errss << "Invalid USERLIST PTY command '" << cmdline << "'. "
               "Usage: USERLIST RELOAD [DL|WW|ALL] [<file>] [<section>] [<beginMarker>] [<endMarker>]";
      goto write_status;
    }
    std::transform(subcmd.begin(), subcmd.end(), subcmd.begin(), ::toupper);
    if (subcmd != "RELOAD") {
      errss << "Invalid USERLIST PTY command '" << cmdline << "'. "
               "Usage: USERLIST RELOAD [DL|WW|ALL] [<file>] [<section>] [<beginMarker>] [<endMarker>]";
      goto write_status;
    }

    std::string which; ss >> which;
    std::string fileOverride, sectionOverride, beginOverride, endOverride;
    if (!which.empty() && (which=="DL" || which=="WW" || which=="ALL")) {
      ss >> fileOverride >> sectionOverride >> beginOverride >> endOverride;
    } else {
      fileOverride = which;
      which.clear();
      ss >> sectionOverride >> beginOverride >> endOverride;
    }

    std::string section = "USERS";
    (void)m_cfg->getValue("GLOBAL", "USERLIST_SECTION", section);

    std::string dlFile = "svxreflector.d/users_dl.conf";
    std::string wwFile = "svxreflector.d/users_ww.conf";
    (void)m_cfg->getValue("GLOBAL", "USERLIST_FILE_DL", dlFile);
    (void)m_cfg->getValue("GLOBAL", "USERLIST_FILE_WW", wwFile);

    std::string dlBegin = "### Userlist DL Begin ###";
    std::string dlEnd   = "### Userlist DL End ###";
    std::string wwBegin = "### Userlist WW Begin ###";
    std::string wwEnd   = "### Userlist WW End ###";
    (void)m_cfg->getValue("GLOBAL", "USERLIST_DL_BEGIN", dlBegin);
    (void)m_cfg->getValue("GLOBAL", "USERLIST_DL_END",   dlEnd);
    (void)m_cfg->getValue("GLOBAL", "USERLIST_WW_BEGIN", wwBegin);
    (void)m_cfg->getValue("GLOBAL", "USERLIST_WW_END",   wwEnd);

    bool ok = true;
    auto doReload = [&](const std::string& whichSel){
      if (whichSel=="DL") {
        std::string f = fileOverride.empty()? dlFile : fileOverride;
        std::string s = sectionOverride.empty()? section : sectionOverride;
        std::string b = beginOverride.empty()? dlBegin : beginOverride;
        std::string e = endOverride.empty()?   dlEnd   : endOverride;
        ok &= reloadOneUserFile(*m_cfg, f, s, b, e, g_userlist_prev_keys_dl);
      } else if (whichSel=="WW") {
        std::string f = fileOverride.empty()? wwFile : fileOverride;
        std::string s = sectionOverride.empty()? section : sectionOverride;
        std::string b = beginOverride.empty()? wwBegin : beginOverride;
        std::string e = endOverride.empty()?   wwEnd   : endOverride;
        ok &= reloadOneUserFile(*m_cfg, f, s, b, e, g_userlist_prev_keys_ww);
      }
    };

    if (which.empty() || which=="ALL") {
      ok &= reloadAllUserLists(*m_cfg);
    } else if (which=="DL" || which=="WW") {
      doReload(which);
    } else {
      errss << "USERLIST RELOAD: invalid scope '" << which << "'. Use DL|WW|ALL";
      goto write_status;
    }

    if (!ok) {
      errss << "Userlist reload failed";
      goto write_status;
    }
  }
  else if (cmd == "QSYDENY")
  {
    std::string subcmd;
    if (!(ss >> subcmd)) {
      errss << "Invalid QSYDENY PTY command '" << cmdline << "'. "
               "Usage: QSYDENY RELOAD [<file>]";
      goto write_status;
    }
    std::transform(subcmd.begin(), subcmd.end(), subcmd.begin(), ::toupper);

    if (subcmd == "RELOAD")
    {
      std::string fileOverride;
      ss >> fileOverride;
      if (!fileOverride.empty())
      {
        g_qsy_deny_file = fileOverride;
      }

      if (!loadQsyDenyList(g_qsy_deny_file))
      {
        errss << "QSYDENY reload failed for file '" << g_qsy_deny_file << "'";
        goto write_status;
      }
    }
    else
    {
      errss << "Invalid QSYDENY PTY command '" << cmdline << "'. "
               "Usage: QSYDENY RELOAD [<file>]";
      goto write_status;
    }
  }
  else if (cmd == "TG")
  {
    std::string subcmd;
    if (!(ss >> subcmd)) {
      errss << "Invalid TG PTY command '" << cmdline << "'. "
               "Usage: TG RELOAD [<file>]";
      goto write_status;
    }
    std::transform(subcmd.begin(), subcmd.end(), subcmd.begin(), ::toupper);

    if (subcmd == "RELOAD")
    {
      std::string fileOverride;
      ss >> fileOverride;
      if (!fileOverride.empty())
      {
        g_tg_handling_file = fileOverride;
      }

      if (!loadTgHandlingFile(*m_cfg, g_tg_handling_file))
      {
        errss << "TG reload failed for file '" << g_tg_handling_file << "'";
        goto write_status;
      }
    }
    else
    {
      errss << "Invalid TG PTY command '" << cmdline << "'. "
               "Usage: TG RELOAD [<file>]";
      goto write_status;
    }
  }
  else if (cmd == "CA")
  {
    std::string subcmd;
    if (!(ss >> subcmd))
    {
      errss << "Invalid CA PTY command '" << cmdline << "'. "
               "Usage: CA PENDING|SIGN <callsign>|LS|RM <callsign>";
      goto write_status;
    }
    std::transform(subcmd.begin(), subcmd.end(), subcmd.begin(), ::toupper);
    if (subcmd == "SIGN")
    {
      std::string cn;
      if (!(ss >> cn))
      {
        errss << "Invalid CA SIGN PTY command '" << cmdline << "'. "
                 "Usage: CA SIGN <callsign>";
        goto write_status;
      }
      auto cert = signClientCsr(cn);
      if (!cert.isNull())
      {
        std::cout << "---------- Signed Client Certificate ----------"
                  << std::endl;
        cert.print(" ");
        std::cout << "-----------------------------------------------"
                  << std::endl;
      }
      else
      {
        errss << "Certificate signing failed";
      }
    }
    else if (subcmd == "RM")
    {
      std::string cn;
      if (!(ss >> cn))
      {
        errss << "Invalid CA RM PTY command '" << cmdline << "'. "
                 "Usage: CA RM <callsign>";
        goto write_status;
      }
      if (removeClientCert(cn))

      {
        std::cout << cn << ": Removed client certificate and CSR"
                  << std::endl;
      }
      else
      {
        errss << "Failed to remove certificate and CSR for '" << cn << "'";
      }
    }
    else if (subcmd == "LS")
    {
      errss << "Not yet implemented";
    }
    else if (subcmd == "PENDING")
    {
      errss << "Not yet implemented";
    }
    else
    {
      errss << "Invalid CA PTY command '" << cmdline << "'. "
               "Usage: CA PENDING|SIGN <callsign>|LS|RM <callsign>";
      goto write_status;
    }
  }
  else
  {
    errss << "Unknown PTY command '" << cmdline
          << "'. Valid commands are: CFG, NODE, USERLIST, QSYDENY, TG, CA";
  }

write_status:
  if (!errss.str().empty())
  {
    std::cerr << "*** ERROR: " << errss.str() << std::endl;
    m_cmd_pty->write(std::string("ERR:") + errss.str() + "\n");
    return;
  }
  m_cmd_pty->write("OK\n");
} /* Reflector::ctrlPtyDataReceived */


void Reflector::cfgUpdated(const std::string& section, const std::string& tag)
{
  std::string value;
  if (!m_cfg->getValue(section, tag, value))
  {
    std::cout << "*** ERROR: Failed to read updated configuration variable '"
              << section << "/" << tag << "'" << std::endl;
    return;
  }

  if (section == "GLOBAL")
  {
    if (tag == "SQL_TIMEOUT_BLOCKTIME")
    {
      unsigned t = TGHandler::instance()->sqlTimeoutBlocktime();
      if (!SvxLink::setValueFromString(t, value))
      {
        std::cout << "*** ERROR: Failed to set updated configuration "
                     "variable '" << section << "/" << tag << "'" << std::endl;
        return;
      }
      TGHandler::instance()->setSqlTimeoutBlocktime(t);
    }
    else if (tag == "SQL_TIMEOUT")
    {
      unsigned t = TGHandler::instance()->sqlTimeout();
      if (!SvxLink::setValueFromString(t, value))
      {
        std::cout << "*** ERROR: Failed to set updated configuration "
                     "variable '" << section << "/" << tag << "'" << std::endl;
        return;
      }
      TGHandler::instance()->setSqlTimeout(t);
    }
  }
} /* Reflector::cfgUpdated */


bool Reflector::loadCertificateFiles(void)
{
  if (!buildPath("GLOBAL", "CERT_PKI_DIR", SVX_LOCAL_STATE_DIR, m_pki_dir) ||
      !buildPath("GLOBAL", "CERT_CA_KEYS_DIR", m_pki_dir, m_keys_dir) ||
      !buildPath("GLOBAL", "CERT_CA_PENDING_CSRS_DIR", m_pki_dir,
                 m_pending_csrs_dir) ||
      !buildPath("GLOBAL", "CERT_CA_CSRS_DIR", m_pki_dir, m_csrs_dir) ||
      !buildPath("GLOBAL", "CERT_CA_CERTS_DIR", m_pki_dir, m_certs_dir))
  {
    return false;
  }

  if (!loadRootCAFiles() || !loadSigningCAFiles() ||
      !loadServerCertificateFiles())
  {
    return false;
  }

  if (!m_cfg->getValue("GLOBAL", "CERT_CA_BUNDLE", m_ca_bundle_file))
  {
    m_ca_bundle_file = m_pki_dir + "/ca-bundle.crt";
  }
  if (access(m_ca_bundle_file.c_str(), F_OK) != 0)
  {
    if (!ensureDirectoryExist(m_ca_bundle_file) ||
        !m_ca_cert.writePemFile(m_ca_bundle_file))
    {
      std::cout << "*** ERROR: Failed to write CA bundle file '"
                << m_ca_bundle_file << "'" << std::endl;
      return false;
    }
  }
  if (!m_ssl_ctx.setCaCertificateFile(m_ca_bundle_file))
  {
    std::cout << "*** ERROR: Failed to read CA certificate bundle '"
              << m_ca_bundle_file << "'" << std::endl;
    return false;
  }

  struct stat st;
  if (stat(m_ca_bundle_file.c_str(), &st) != 0)
  {
    auto errstr = SvxLink::strError(errno);
    std::cerr << "*** ERROR: Failed to read CA file from '"
              << m_ca_bundle_file << "': " << errstr << std::endl;
    return false;
  }
  auto bundle = caBundlePem();
  m_ca_size = bundle.size();
  Async::Digest ca_dgst;
  if (!ca_dgst.md(m_ca_md, MsgCABundle::MD_ALG, bundle))
  {
    std::cerr << "*** ERROR: CA bundle checksumming failed"
              << std::endl;
    return false;
  }
  ca_dgst.signInit(MsgCABundle::MD_ALG, m_issue_ca_pkey);
  m_ca_sig = ca_dgst.sign(bundle);

  // --- Blockliste initialisieren / laden ---
  {
    std::string cfg_blockfile;
    if (!m_cfg->getValue("GLOBAL", "BLOCKLIST_FILE", cfg_blockfile) || cfg_blockfile.empty())
    {
      g_blocked_file = m_pki_dir + "/blocked.json";
    }
    else
    {
      g_blocked_file = cfg_blockfile;
    }

    (void)loadBlockedList();

    if (access(g_blocked_file.c_str(), F_OK) != 0)
    {
      if (!saveBlockedList())
      {
        std::cerr << "*** WARNING: Failed to create blocked list file '"
                  << g_blocked_file
                  << "'. Check directory permissions or choose a writable path."
                  << std::endl;
      }
    }
  }

  return true;
} /* Reflector::loadCertificateFiles */


bool Reflector::loadServerCertificateFiles(void)
{
  std::string cert_cn;
  if (!m_cfg->getValue("SERVER_CERT", "COMMON_NAME", cert_cn) ||
      cert_cn.empty())
  {
    std::cerr << "*** ERROR: The 'SERVER_CERT/COMMON_NAME' variable is "
                 "unset which is needed for certificate signing request "
                 "generation." << std::endl;
    return false;
  }

  std::string keyfile;
  if (!m_cfg->getValue("SERVER_CERT", "KEYFILE", keyfile))
  {
    keyfile = m_keys_dir + "/" + cert_cn + ".key";
  }
  Async::SslKeypair pkey;
  if (access(keyfile.c_str(), F_OK) != 0)
  {
    std::cout << "Server private key file not found. Generating '"
              << keyfile << "'" << std::endl;
    if (!generateKeyFile(pkey, keyfile))
    {
      return false;
    }
  }
  else if (!pkey.readPrivateKeyFile(keyfile))
  {
    std::cerr << "*** ERROR: Failed to read private key file from '"
              << keyfile << "'" << std::endl;
    return false;
  }

  if (!m_cfg->getValue("SERVER_CERT", "CRTFILE", m_crtfile))
  {
    m_crtfile = m_certs_dir + "/" + cert_cn + ".crt";
  }
  Async::SslX509 cert;
  bool generate_cert = (access(m_crtfile.c_str(), F_OK) != 0);
  if (!generate_cert)
  {
    generate_cert = !cert.readPemFile(m_crtfile) ||
                    !cert.verify(m_issue_ca_pkey);
    if (generate_cert)
    {
      std::cerr << "*** WARNING: Failed to read server certificate "
                   "from '" << m_crtfile << "' or the cert is invalid. "
                   "Generating new certificate." << std::endl;
      cert.clear();
    }
    else
    {
      int days=0, seconds=0;
      cert.validityTime(days, seconds);
      time_t tnow = time(NULL);
      time_t renew_time = tnow + (days*24*3600 + seconds)*RENEW_AFTER;
      if (!cert.timeIsWithinRange(tnow, renew_time))
      {
        std::cerr << "Time to renew the server certificate '" << m_crtfile
                  << "'. It's valid until "
                  << cert.notAfterLocaltimeString() << "." << std::endl;
        cert.clear();
        generate_cert = true;
      }
    }
  }
  if (generate_cert)
  {
    std::string csrfile;
    if (!m_cfg->getValue("SERVER_CERT", "CSRFILE", csrfile))
    {
      csrfile = m_csrs_dir + "/" + cert_cn + ".csr";
    }
    Async::SslCertSigningReq req;
    std::cout << "Generating server certificate signing request file '"
              << csrfile << "'" << std::endl;
    req.setVersion(Async::SslCertSigningReq::VERSION_1);
    req.addSubjectName("CN", cert_cn);
    Async::SslX509Extensions req_exts;
    req_exts.addBasicConstraints("critical, CA:FALSE");
    req_exts.addKeyUsage(
        "critical, digitalSignature, keyEncipherment, keyAgreement");
    req_exts.addExtKeyUsage("serverAuth");
    std::stringstream csr_san_ss;
    csr_san_ss << "DNS:" << cert_cn;
    std::string cert_san_str;
    if (m_cfg->getValue("SERVER_CERT", "SUBJECT_ALT_NAME", cert_san_str) &&
        !cert_san_str.empty())
    {
      csr_san_ss << "," << cert_san_str;
    }
    std::string email_address;
    if (m_cfg->getValue("SERVER_CERT", "EMAIL_ADDRESS", email_address) &&
        !email_address.empty())
    {
      csr_san_ss << ",email:" << email_address;
    }
    req_exts.addSubjectAltNames(csr_san_ss.str());
    req.addExtensions(req_exts);
    req.setPublicKey(pkey);
    req.sign(pkey);
    if (!req.writePemFile(csrfile))
    {
      std::cerr << "*** WARNING: Failed to write server certificate "
                   "signing request file to '" << csrfile << "'"
                << std::endl;
    }
    std::cout << "-------- Certificate Signing Request -------" << std::endl;
    req.print();
    std::cout << "--------------------------------------------" << std::endl;

    std::cout << "Generating server certificate file '" << m_crtfile << "'"
              << std::endl;
    cert.setSerialNumber();
    cert.setVersion(Async::SslX509::VERSION_3);
    cert.setIssuerName(m_issue_ca_cert.subjectName());
    cert.setSubjectName(req.subjectName());
    cert.setValidityTime(CERT_VALIDITY_DAYS);
    cert.addExtensions(req.extensions());
    cert.setPublicKey(pkey);
    cert.sign(m_issue_ca_pkey);
    assert(cert.verify(m_issue_ca_pkey));
    if (!ensureDirectoryExist(m_crtfile) || !cert.writePemFile(m_crtfile) ||
        !m_issue_ca_cert.appendPemFile(m_crtfile))
    {
      std::cout << "*** ERROR: Failed to write server certificate file '"
                << m_crtfile << "'" << std::endl;
      return false;
    }
  }
  std::cout << "------------ Server Certificate ------------" << std::endl;
  cert.print();
  std::cout << "--------------------------------------------" << std::endl;

  if (!m_ssl_ctx.setCertificateFiles(keyfile, m_crtfile))
  {
      std::cout << "*** ERROR: Failed to read and verify key ('"
                << keyfile << "') and certificate ('"
                << m_crtfile << "') files. "
                << "If key- and cert-file does not match, the certificate "
                   "is invalid for any other reason, you need "
                   "to remove the cert file in order to trigger the "
                   "generation of a new certificate signing request."
                   "Then the CSR need to be signed by the CA which creates a "
                   "valid certificate."
                << std::endl;
      return false;
  }

  startCertRenewTimer(cert, m_renew_cert_timer);

  return true;
} /* Reflector::loadServerCertificateFiles */


bool Reflector::generateKeyFile(Async::SslKeypair& pkey,
                                const std::string& keyfile)
{
  pkey.generate(2048);
  if (!ensureDirectoryExist(keyfile) || !pkey.writePrivateKeyFile(keyfile))
  {
    std::cerr << "*** ERROR: Failed to write private key file to '"
              << keyfile << "'" << std::endl;
    return false;
  }
  return true;
} /* Reflector::generateKeyFile */


bool Reflector::loadRootCAFiles(void)
{
  std::string ca_keyfile;
  if (!m_cfg->getValue("ROOT_CA", "KEYFILE", ca_keyfile))
  {
    ca_keyfile = m_keys_dir + "/svxreflector_root_ca.key";
  }
  if (access(ca_keyfile.c_str(), F_OK) != 0)
  {
    std::cout << "Root CA private key file not found. Generating '"
              << ca_keyfile << "'" << std::endl;
    if (!m_ca_pkey.generate(4096))
    {
      std::cout << "*** ERROR: Failed to generate root CA key" << std::endl;
      return false;
    }
    if (!ensureDirectoryExist(ca_keyfile) ||
        !m_ca_pkey.writePrivateKeyFile(ca_keyfile))
    {
      std::cerr << "*** ERROR: Failed to write root CA private key file to '"
                 << ca_keyfile << "'" << std::endl;
      return false;
    }
  }
  else if (!m_ca_pkey.readPrivateKeyFile(ca_keyfile))
  {
    std::cerr << "*** ERROR: Failed to read root CA private key file from '"
              << ca_keyfile << "'" << std::endl;
    return false;
  }

  std::string ca_crtfile;
  if (!m_cfg->getValue("ROOT_CA", "CRTFILE", ca_crtfile))
  {
    ca_crtfile = m_certs_dir + "/svxreflector_root_ca.crt";
  }
  bool generate_ca_cert = (access(ca_crtfile.c_str(), F_OK) != 0);
  if (!generate_ca_cert)
  {
    if (!m_ca_cert.readPemFile(ca_crtfile) ||
        !m_ca_cert.verify(m_ca_pkey) ||
        !m_ca_cert.timeIsWithinRange())
    {
      std::cerr << "*** ERROR: Failed to read root CA certificate file "
                   "from '" << ca_crtfile << "' or the cert is invalid."
                << std::endl;
      return false;
    }
  }
  if (generate_ca_cert)
  {
    std::cout << "Generating root CA certificate file '" << ca_crtfile << "'"
              << std::endl;
    m_ca_cert.setSerialNumber();
    m_ca_cert.setVersion(Async::SslX509::VERSION_3);

    std::string value;
    value = "SvxReflector Root CA";
    (void)m_cfg->getValue("ROOT_CA", "COMMON_NAME", value);
    if (value.empty())
    {
      std::cerr << "*** ERROR: The 'ROOT_CA/COMMON_NAME' variable is "
                   "unset which is needed for root CA certificate generation."
                << std::endl;
      return false;
    }
    m_ca_cert.addIssuerName("CN", value);
    if (m_cfg->getValue("ROOT_CA", "ORG_UNIT", value) &&
        !value.empty())
    {
      m_ca_cert.addIssuerName("OU", value);
    }
    if (m_cfg->getValue("ROOT_CA", "ORG", value) && !value.empty())
    {
      m_ca_cert.addIssuerName("O", value);
    }
    if (m_cfg->getValue("ROOT_CA", "LOCALITY", value) && !value.empty())
    {
      m_ca_cert.addIssuerName("L", value);
    }
    if (m_cfg->getValue("ROOT_CA", "STATE", value) && !value.empty())
    {
      m_ca_cert.addIssuerName("ST", value);
    }
    if (m_cfg->getValue("ROOT_CA", "COUNTRY", value) && !value.empty())
    {
      m_ca_cert.addIssuerName("C", value);
    }
    m_ca_cert.setSubjectName(m_ca_cert.issuerName());
    Async::SslX509Extensions ca_exts;
    ca_exts.addBasicConstraints("critical, CA:TRUE");
    ca_exts.addKeyUsage("critical, cRLSign, digitalSignature, keyCertSign");
    if (m_cfg->getValue("ROOT_CA", "EMAIL_ADDRESS", value) &&
        !value.empty())
    {
      ca_exts.addSubjectAltNames("email:" + value);
    }
    m_ca_cert.addExtensions(ca_exts);
    m_ca_cert.setValidityTime(ROOT_CA_VALIDITY_DAYS);
    m_ca_cert.setPublicKey(m_ca_pkey);
    m_ca_cert.sign(m_ca_pkey);
    if (!m_ca_cert.writePemFile(ca_crtfile))
    {
      std::cout << "*** ERROR: Failed to write root CA certificate file '"
                << ca_crtfile << "'" << std::endl;
      return false;
    }
  }
  std::cout << "----------- Root CA Certificate ------------" << std::endl;
  m_ca_cert.print();
  std::cout << "--------------------------------------------" << std::endl;

  return true;
} /* Reflector::loadRootCAFiles */


bool Reflector::loadSigningCAFiles(void)
{
  std::string ca_keyfile;
  if (!m_cfg->getValue("ISSUING_CA", "KEYFILE", ca_keyfile))
  {
    ca_keyfile = m_keys_dir + "/svxreflector_issuing_ca.key";
  }
  if (access(ca_keyfile.c_str(), F_OK) != 0)
  {
    std::cout << "Issuing CA private key file not found. Generating '"
              << ca_keyfile << "'" << std::endl;
    if (!m_issue_ca_pkey.generate(2048))
    {
      std::cout << "*** ERROR: Failed to generate CA key" << std::endl;
      return false;
    }
    if (!ensureDirectoryExist(ca_keyfile) ||
        !m_issue_ca_pkey.writePrivateKeyFile(ca_keyfile))
    {
      std::cerr << "*** ERROR: Failed to write issuing CA private key file "
                   "to '" << ca_keyfile << "'" << std::endl;
      return false;
    }
  }
  else if (!m_issue_ca_pkey.readPrivateKeyFile(ca_keyfile))
  {
    std::cerr << "*** ERROR: Failed to read issuing CA private key file "
                 "from '" << ca_keyfile << "'" << std::endl;
    return false;
  }

  std::string ca_crtfile;
  if (!m_cfg->getValue("ISSUING_CA", "CRTFILE", ca_crtfile))
  {
    ca_crtfile = m_certs_dir + "/svxreflector_issuing_ca.crt";
  }
  bool generate_ca_cert = (access(ca_crtfile.c_str(), F_OK) != 0);
  if (!generate_ca_cert)
  {
    generate_ca_cert = !m_issue_ca_cert.readPemFile(ca_crtfile) ||
                       !m_issue_ca_cert.verify(m_ca_pkey) ||
                       !m_issue_ca_cert.timeIsWithinRange();
    if (generate_ca_cert)
    {
      std::cerr << "*** WARNING: Failed to read issuing CA certificate "
                   "from '" << ca_crtfile << "' or the cert is invalid. "
                   "Generating new certificate." << std::endl;
      m_issue_ca_cert.clear();
    }
    else
    {
      int days=0, seconds=0;
      m_issue_ca_cert.validityTime(days, seconds);
      time_t tnow = time(NULL);
      time_t renew_time = tnow + (days*24*3600 + seconds)*RENEW_AFTER;
      if (!m_issue_ca_cert.timeIsWithinRange(tnow, renew_time))
      {
        std::cerr << "Time to renew the issuing CA certificate '"
                  << ca_crtfile << "'. It's valid until "
                  << m_issue_ca_cert.notAfterLocaltimeString() << "."
                  << std::endl;
        m_issue_ca_cert.clear();
        generate_ca_cert = true;
      }
    }
  }

  if (generate_ca_cert)
  {
    std::string ca_csrfile;
    if (!m_cfg->getValue("ISSUING_CA", "CSRFILE", ca_csrfile))
    {
      ca_csrfile = m_csrs_dir + "/svxreflector_issuing_ca.csr";
    }
    std::cout << "Generating issuing CA CSR file '" << ca_csrfile
              << "'" << std::endl;
    Async::SslCertSigningReq csr;
    csr.setVersion(Async::SslCertSigningReq::VERSION_1);
    std::string value;
    value = "SvxReflector Issuing CA";
    (void)m_cfg->getValue("ISSUING_CA", "COMMON_NAME", value);
    if (value.empty())
    {
      std::cerr << "*** ERROR: The 'ISSUING_CA/COMMON_NAME' variable is "
                   "unset which is needed for issuing CA certificate "
                   "generation." << std::endl;
      return false;
    }
    csr.addSubjectName("CN", value);
    if (m_cfg->getValue("ISSUING_CA", "ORG_UNIT", value) &&
        !value.empty())
    {
      csr.addSubjectName("OU", value);
    }
    if (m_cfg->getValue("ISSUING_CA", "ORG", value) && !value.empty())
    {
      csr.addSubjectName("O", value);
    }
    if (m_cfg->getValue("ISSUING_CA", "LOCALITY", value) && !value.empty())
    {
      csr.addSubjectName("L", value);
    }
    if (m_cfg->getValue("ISSUING_CA", "STATE", value) && !value.empty())
    {
      csr.addSubjectName("ST", value);
    }
    if (m_cfg->getValue("ISSUING_CA", "COUNTRY", value) && !value.empty())
    {
      csr.addSubjectName("C", value);
    }
    Async::SslX509Extensions exts;
    exts.addBasicConstraints("critical, CA:TRUE, pathlen:0");
    exts.addKeyUsage("critical, cRLSign, digitalSignature, keyCertSign");
    if (m_cfg->getValue("ISSUING_CA", "EMAIL_ADDRESS", value) &&
        !value.empty())
    {
      exts.addSubjectAltNames("email:" + value);
    }
    csr.addExtensions(exts);
    csr.setPublicKey(m_issue_ca_pkey);
    csr.sign(m_issue_ca_pkey);
    if (!csr.writePemFile(ca_csrfile))
    {
      std::cout << "*** ERROR: Failed to write issuing CA CSR file '"
                << ca_csrfile << "'" << std::endl;
      return false;
    }

    std::cout << "Generating issuing CA certificate file '" << ca_crtfile
              << "'" << std::endl;
    m_issue_ca_cert.setSerialNumber();
    m_issue_ca_cert.setVersion(Async::SslX509::VERSION_3);
    m_issue_ca_cert.setSubjectName(csr.subjectName());
    m_issue_ca_cert.addExtensions(csr.extensions());
    m_issue_ca_cert.setValidityTime(ISSUING_CA_VALIDITY_DAYS);
    m_issue_ca_cert.setPublicKey(m_issue_ca_pkey);
    m_issue_ca_cert.setIssuerName(m_ca_cert.subjectName());
    m_issue_ca_cert.sign(m_ca_pkey);
    if (!m_issue_ca_cert.writePemFile(ca_crtfile))
    {
      std::cout << "*** ERROR: Failed to write issuing CA certificate file '"
                << ca_crtfile << "'" << std::endl;
      return false;
    }
  }
  std::cout << "---------- Issuing CA Certificate ----------" << std::endl;
  m_issue_ca_cert.print();
  std::cout << "--------------------------------------------" << std::endl;

  startCertRenewTimer(m_issue_ca_cert, m_renew_issue_ca_cert_timer);

  return true;
} /* Reflector::loadSigningCAFiles */


bool Reflector::onVerifyPeer(TcpConnection *con, bool preverify_ok,
                             X509_STORE_CTX *x509_store_ctx)
{
  Async::SslX509 cert(*x509_store_ctx);
  preverify_ok = preverify_ok && !cert.isNull();
  preverify_ok = preverify_ok && !cert.commonName().empty();
  if (!preverify_ok)
  {
    std::cout << "*** ERROR: Certificate verification failed for client"
              << std::endl;
    std::cout << "------------ Client Certificate -------------" << std::endl;
    cert.print();
    std::cout << "---------------------------------------------" << std::endl;
  }

  return preverify_ok;
} /* Reflector::onVerifyPeer */


bool Reflector::buildPath(const std::string& sec,    const std::string& tag,
                          const std::string& defdir, std::string& defpath)
{
  bool isdir = (defpath.back() == '/');
  std::string path(defpath);
  if (!m_cfg->getValue(sec, tag, path) || path.empty())
  {
    path = defpath;
  }
  if ((path.front() != '/') && (path.front() != '.'))
  {
    path = defdir + "/" + defpath;
  }
  if (!ensureDirectoryExist(path))
  {
    return false;
  }
  if (isdir && (path.back() == '/'))
  {
    defpath = path.substr(0, path.size()-1);
  }
  else
  {
    defpath = std::move(path);
  }
  return true;
} /* Reflector::buildPath */


bool Reflector::removeClientCert(const std::string& cn)
{
  std::cout << "### Reflector::removeClientCert: cn=" << cn << std::endl;
  return true;
} /* Reflector::removeClientCert */


void Reflector::runCAHook(const Async::Exec::Environment& env)
{
  auto ca_hook_cmd = m_cfg->getValue("GLOBAL", "CERT_CA_HOOK");
  if (!ca_hook_cmd.empty())
  {
    auto ca_hook = new Async::Exec(ca_hook_cmd);
    ca_hook->addEnvironmentVars(env);
    ca_hook->setTimeout(300);
    ca_hook->stdoutData.connect(
        [=](const char* buf, int cnt)
        {
          std::cout << buf;
        });
    ca_hook->stderrData.connect(
        [=](const char* buf, int cnt)
        {
          std::cerr << buf;
        });
    ca_hook->exited.connect(
        [=](void) {
          if (ca_hook->ifExited())
          {
            if (ca_hook->exitStatus() != 0)
            {
              std::cerr << "*** ERROR: CA hook exited with exit status "
                        << ca_hook->exitStatus() << std::endl;
            }
          }
          else if (ca_hook->ifSignaled())
          {
            std::cerr << "*** ERROR: CA hook exited with signal "
                      << ca_hook->termSig() << std::endl;
          }
          Async::Application::app().runTask([=]{ delete ca_hook; });
        });
    ca_hook->run();
  }
} /* Reflector::runCAHook */


/*
 * This file has not been truncated
 */
