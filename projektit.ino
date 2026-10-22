#include <FS.h>
using namespace fs;
#include <WiFi.h> 
#include <WebServer.h>
#include <HTTPClient.h>
#include <WireGuard-ESP32.h>
#include <lwip/tcpip.h>
#include <lwip/netif.h>
#include <lwip/ip4_addr.h>
#include <time.h>
#include <Preferences.h> 
#include <TFT_eSPI.h>
#include <lvgl.h>
#include <math.h>

TFT_eSPI tft = TFT_eSPI();
Preferences preferences;
WebServer server(80);
static WireGuard wg;

/* === 1. NASTAVENÍ WI-FI, WIREGUARD VPN A DOMÁCÍHO SERVERU === */
// Volitelné: Pokud sem napíšeš svou Wi-Fi, ESP32 se připojí hned po zapnutí:
const char* DEFAULT_WIFI_SSID = ""; 
const char* DEFAULT_WIFI_PASS = ""; 

// Klíče vygenerované příkazem `wg genkey` na Ubuntu:
const char* WG_PRIVATE_KEY    = "SEM_VLOZ_ESP32_PRIVATE_KEY";
const char* WG_PUBLIC_KEY     = "SEM_VLOZ_SERVER_PUBLIC_KEY";
// IP adresa tvého Ubuntu serveru (doma lokální IP např. "192.168.1.50", venku veřejná IP):
const char* WG_ENDPOINT_ADDR  = "192.168.1.100"; 
const uint16_t WG_ENDPOINT_PORT = 51820;
const IPAddress WG_LOCAL_IP(10, 8, 0, 50);

// IP adresa Ubuntu serveru uvnitř VPN tunelu (má automatický fallback na WG_ENDPOINT_ADDR):
const char* HOME_SERVER_HOST  = "10.8.0.1"; 
const uint16_t HOME_SERVER_PORT = 8085;

/* === 2. DATOVÉ STRUKTURY A STAVOVÝ AUTOMAT APLIKACÍ === */
enum AppID : uint8_t {
    APP_LAUNCHER = 0,
    APP_RADAR    = 1,
    APP_PAINT    = 2,
    APP_DOOM     = 3,
    APP_HOME     = 4,
    APP_AI       = 5,
    APP_WIFI     = 6
};

volatile AppID activeApp = APP_LAUNCHER;

const int TRAIL_LEN = 6;
const int MAX_STROKES = 400;
const int WEB_DRAW_Q_SIZE = 64;
const int MAX_ECHOS = 10;

struct StrokeSegment {
    uint16_t x1, y1, x2, y2;
    uint8_t flags; 
};

struct RawReading {
    bool valid = false;
    bool matched = false;
    int16_t x_mm = 0, y_mm = 0, speed_cms = 0;
    uint16_t gate_mm = 0;
    int dist_cm = 0;
    int sx = 0, sy = 0;
    float angle_deg = 0.0f;
};

struct RadarTarget {
    bool active = false; 
    int16_t x = 0, y = 0, dist = 0, speed = 0;
    int16_t raw_x = 0, raw_y = 0; 
    uint16_t gate_res_mm = 0;   
    float angle_deg = 0.0f;     
    unsigned long lastTime = 0;

    float smoothX = 0.0f, smoothY = 0.0f, smoothR = 6.0f; 
    float velX = 0.0f, velY = 0.0f;
    float smoothWorldX = 0.0f, smoothWorldY = 0.0f; 

    int16_t lastX = 0, lastY = 0, lastR = 0, lastGateR = 0;
    int16_t lastVecX = 0, lastVecY = 0;
    bool hadVec = false;
    bool hadLockBox = false;

    int16_t trailX[TRAIL_LEN];
    int16_t trailY[TRAIL_LEN];
    int16_t lastTrailX[TRAIL_LEN];
    int16_t lastTrailY[TRAIL_LEN];
    uint8_t trailCount = 0;
    uint8_t lastTrailCount = 0;
    unsigned long lastTrailTime = 0;
};

struct PulseEcho {
    bool active = false;
    int16_t x = 0, y = 0;
    int16_t lastX = 0, lastY = 0;
    int16_t r = 0, lastR = 0;
    int16_t dist = 0;
    uint16_t baseColor = 0;
    int16_t life = 0; 
};

enum ParserState { HEAD1, HEAD2, HEAD3, HEAD4, DATA, TAIL1, TAIL2 };

/* === 3. DYNAMICKÉ UKAZATELE NA HEAPU === */
StrokeSegment* strokeHistory = NULL; 
StrokeSegment* webDrawQ      = NULL; 
float*         zBuffer       = NULL; 
PulseEcho*     echos         = NULL; 
char*          jsonBuf       = NULL; 

/* === 4. MEZIJADERNÁ KOMUNIKACE (Jádro 0 <-> Jádro 1) === */
char current_ssid[64] = "";
char current_pass[64] = "";
char scan_options_buf[384] = "Hledam site...\nProsim cekejte";

volatile bool wifi_connected = false; 
volatile bool wg_connected = false;
volatile bool status_bar_dirty = true;
volatile bool wifi_connect_request = false; 
volatile bool wifi_scan_request = false;    
volatile bool wifi_scan_ready = false;      
char wifi_ip_str[36] = "Wi-Fi: OFF";
char lan_status_detail[64] = "Wi-Fi nepripojeno (Otevri Wi-Fi)";

volatile int remote_cmd = 0;
volatile int web_doom_action = 0;
volatile bool paint_ui_dirty = false;
volatile bool paint_needs_restore = false;
volatile int web_lock_req_x = -1;
volatile int web_lock_req_y = -1;

char remote_toast_text[64] = "";
volatile bool remote_toast_pending = false;
unsigned long toast_hide_time = 0;

/* === 5. SMART HOME & LOKÁLNÍ AI PROMĚNNÉ === */
const int RELAY_COUNT = 4;
const char* relayNames[RELAY_COUNT] = {"Hlavni Svetlo", "LED Pasek", "3D Tiskarna", "Ventilator"};
volatile bool relayStates[RELAY_COUNT] = {false, false, false, false};
volatile int pending_relay_toggle = -1; 
volatile bool relay_ui_dirty = false;

char ai_prompt_buf[160] = "";
char ai_response_buf[800] = "AI Agent pripraven.\nTapni do pole dole pro klavesnici nebo zvol rychly povel.";
volatile bool ai_request_pending = false;
volatile bool ai_response_dirty = false;
volatile bool ai_is_streaming = false;

/* === 6. HARDWARE A OVLADAČE === */
#define RADAR_RX 2 
#define RADAR_TX 4 
const long RADAR_BAUD_RATE = 256000; 

static const uint16_t screenWidth  = 320;
static const uint16_t screenHeight = 240;
int centerX = screenWidth / 2;
int centerY = screenHeight;

static lv_disp_draw_buf_t draw_buf;
static lv_color_t buf[ screenWidth * screenHeight / 12 ]; 

/* === UI PROMĚNNÉ === */
lv_obj_t * current_screen = NULL;
lv_obj_t * wifi_icon = NULL; 
lv_obj_t * launcher_ip_label = NULL;
lv_obj_t * toast_box = NULL;
lv_obj_t * toast_label = NULL;
lv_obj_t * btn_mode_label = NULL;
lv_obj_t * kb = NULL; 
lv_obj_t * dd_ssid = NULL; 
lv_obj_t * ta_pass = NULL;
lv_obj_t * color_btns[4] = {NULL, NULL, NULL, NULL};
lv_obj_t * relay_btns[RELAY_COUNT] = {NULL, NULL, NULL, NULL};
lv_obj_t * relay_lbls[RELAY_COUNT] = {NULL, NULL, NULL, NULL};

lv_obj_t * ai_ta_out = NULL;
lv_obj_t * ai_ta_in = NULL;
lv_obj_t * ai_btn_send = NULL;
lv_obj_t * ai_qbtns[4] = {NULL, NULL, NULL, NULL};

/* === NASTAVENÍ RADARU === */
volatile int current_max_y_mm = 8000;   
volatile bool radar_multi_mode = true;  
bool radar_pulse_mode = false;
bool radar_needs_grid = false;
const int MIN_DIST_CM = 15;             
const int MAX_SPEED_CMS = 120;          
const unsigned long KEEPALIVE_MS = 450; 
const int RADAR_R_MAX = 192;            
const float SMOOTH_POS = 0.22f;         
const float SMOOTH_SIZE = 0.15f;        
const float PULSE_SPEED = 3.5f;        

volatile int radar_fps = 0;
int radar_frame_counter = 0;
unsigned long last_fps_calc = 0;

#define RADAR_BG      TFT_BLACK
#define RADAR_GRID    tft.color565(0, 65, 0)
#define RADAR_CONE    tft.color565(0, 160, 60)
#define SWEEP_COLOR   tft.color565(0, 255, 0)
#define LOCK_COLOR    tft.color565(0, 255, 255)

/* === PROMĚNNÉ PRO 3D ENGINE === */
const int VIEW_TOP = 36; 
const int VIEW_HEIGHT = screenHeight - VIEW_TOP;
const int VIEW_HORIZON = VIEW_TOP + (VIEW_HEIGHT / 2);

const int mapW = 8;
const int mapH = 8;
uint8_t worldMap[mapH][mapW] = {
  {1,2,1,2,3,2,1,2},
  {1,0,0,0,0,0,0,2},
  {2,0,0,0,0,0,0,1},
  {1,0,0,0,0,0,0,2},
  {2,0,0,0,0,0,0,1},
  {1,0,0,0,0,0,0,2},
  {2,0,0,0,0,0,0,1},
  {1,2,1,2,1,2,1,2}
};

const float RADAR_VIRTUAL_X = 4.5f; 
const float RADAR_VIRTUAL_Y = 1.0f; 

float playerX = 4.5f;
float playerY = 6.5f;
float playerAngle = -1.570796f; 
int aimedTargetGlobal = -1;

int doom_action = 0; 
float walkTimer = 0.0f; 
float pulseRadius = 0;
float lastPulseRadius = 0;

/* === PROMĚNNÉ PRO MALOVÁNÍ === */
uint16_t paint_color = TFT_WHITE;
volatile int paint_x = -1;
volatile int paint_y = -1;
volatile bool is_drawing = false;
int last_drawn_x = -1;
int last_drawn_y = -1;

volatile uint32_t strokeTotalCount = 0; 
volatile uint32_t paintClearId = 1;     
volatile int webDrawHead = 0;
volatile int webDrawTail = 0;

RadarTarget targets[3];
int locked_target_idx = -1; 

unsigned long lastDataTime = 0; 
ParserState parserState = HEAD1;
byte frameData[24]; 
int dataIdx = 0;

/* === POMOCNÉ FUNKCE === */
uint8_t colorToIndex(uint16_t col) {
    if (col == TFT_RED)   return 1;
    if (col == TFT_GREEN) return 2;
    if (col == TFT_BLUE)  return 3;
    return 0; 
}

uint16_t indexToColor(uint8_t idx) {
    if (idx == 1) return TFT_RED;
    if (idx == 2) return TFT_GREEN;
    if (idx == 3) return TFT_BLUE;
    return TFT_WHITE;
}

void sanitizeJsonString(char* dst, const char* src, size_t maxLen) {
    size_t j = 0;
    for (size_t i = 0; src[i] != '\0' && j + 2 < maxLen; i++) {
        char c = src[i];
        if (c == '"' || c == '\\') c = '\'';
        else if (c == '\n' || c == '\r') c = ' ';
        else if ((uint8_t)c < 32) continue;
        dst[j++] = c;
    }
    dst[j] = '\0';
}

void recordStroke(int x1, int y1, int x2, int y2, uint8_t cIdx, bool fromWeb) {
    if (strokeHistory == NULL) return;
    uint32_t pos = strokeTotalCount % MAX_STROKES;
    strokeHistory[pos].x1 = constrain(x1, 74, 319);
    strokeHistory[pos].y1 = constrain(y1, 0, 239);
    strokeHistory[pos].x2 = constrain(x2, 74, 319);
    strokeHistory[pos].y2 = constrain(y2, 0, 239);
    strokeHistory[pos].flags = (cIdx & 0x03) | (fromWeb ? 0x04 : 0x00);
    strokeTotalCount++;
}

void setRadarHardwareTrackingMode(bool multiTarget) {
    byte enterCfg[] = {0xFD, 0xFC, 0xFB, 0xFA, 0x04, 0x00, 0xFF, 0x00, 0x01, 0x00, 0x04, 0x03, 0x02, 0x01};
    byte multiCmd[] = {0xFD, 0xFC, 0xFB, 0xFA, 0x02, 0x00, 0x90, 0x00, 0x04, 0x03, 0x02, 0x01};
    byte singleCmd[]= {0xFD, 0xFC, 0xFB, 0xFA, 0x02, 0x00, 0x80, 0x00, 0x04, 0x03, 0x02, 0x01};
    byte exitCfg[]  = {0xFD, 0xFC, 0xFB, 0xFA, 0x02, 0x00, 0xFE, 0x00, 0x04, 0x03, 0x02, 0x01};

    Serial2.write(enterCfg, sizeof(enterCfg));
    delay(25);
    if (multiTarget) Serial2.write(multiCmd, sizeof(multiCmd));
    else             Serial2.write(singleCmd, sizeof(singleCmd));
    delay(25);
    Serial2.write(exitCfg, sizeof(exitCfg));
    radar_multi_mode = multiTarget;
}

/* === KOMUNIKACE S DOMÁCÍM SERVEREM (CHYTRÉ SMĚROVÁNÍ VPN / LAN + HTTP/1.0 STREAM) === */
void parseRelaysJson(const String& body) {
    int idx = body.indexOf("[");
    if (idx >= 0 && body.length() >= (unsigned int)(idx + 7)) {
        for (int i = 0; i < RELAY_COUNT; i++) {
            char c = body.charAt(idx + 1 + (i * 2));
            if (c == '1') relayStates[i] = true;
            else if (c == '0') relayStates[i] = false;
        }
        relay_ui_dirty = true;
    }
}

bool tryHttpGetWithFallback(const String& path, String& outBody, int timeoutMs = 550) {
    if (!wifi_connected) return false;
    const char* hosts[2];
    int hostCount = 0;
    if (wg_connected) {
        hosts[hostCount++] = HOME_SERVER_HOST;
    }
    if (strcmp(WG_ENDPOINT_ADDR, HOME_SERVER_HOST) != 0) {
        hosts[hostCount++] = WG_ENDPOINT_ADDR;
    }

    for (int h = 0; h < hostCount; h++) {
        server.handleClient();
        HTTPClient http;
        http.useHTTP10(true);
        String url = "http://" + String(hosts[h]) + ":" + String(HOME_SERVER_PORT) + path;
        http.setConnectTimeout(timeoutMs);
        http.setTimeout(timeoutMs);
        if (http.begin(url)) {
            int code = http.GET();
            if (code == HTTP_CODE_OK) {
                outBody = http.getString();
                http.end();
                return true;
            }
            http.end();
        }
    }
    return false;
}

void syncRelaysFromServerOnCore0() {
    String body;
    if (tryHttpGetWithFallback("/api/relays", body, 500)) {
        parseRelaysJson(body);
    }
}

void executeSmartHomeRelayOnCore0(int relayIdx) {
    if (relayIdx < 0 || relayIdx >= RELAY_COUNT) return;
    bool newState = !relayStates[relayIdx];
    String body;
    String path = "/api/relay?id=" + String(relayIdx) + "&state=" + String(newState ? 1 : 0);
    if (tryHttpGetWithFallback(path, body, 600)) {
        parseRelaysJson(body);
        return;
    }
    relayStates[relayIdx] = newState;
    relay_ui_dirty = true;
}

void executeAIStreamOnCore0() {
    ai_is_streaming = true;
    snprintf(ai_response_buf, sizeof(ai_response_buf), "Ty: %s\nAI: [Spojuji se serverem...]", ai_prompt_buf);
    ai_response_dirty = true;

    bool connectedToHomeServer = false;
    if (wifi_connected) {
        char cleanPrompt[160];
        sanitizeJsonString(cleanPrompt, ai_prompt_buf, sizeof(cleanPrompt));
        String payload = "{\"prompt\":\"" + String(cleanPrompt) + "\"}";

        const char* hosts[2];
        int hostCount = 0;
        if (wg_connected) {
            hosts[hostCount++] = HOME_SERVER_HOST;
        }
        if (strcmp(WG_ENDPOINT_ADDR, HOME_SERVER_HOST) != 0) {
            hosts[hostCount++] = WG_ENDPOINT_ADDR;
        }

        for (int h = 0; h < hostCount && !connectedToHomeServer; h++) {
            server.handleClient();
            HTTPClient http;
            http.useHTTP10(true);
            String url = "http://" + String(hosts[h]) + ":" + String(HOME_SERVER_PORT) + "/api/ai";
            http.setConnectTimeout(1200);
            http.setTimeout(15000);

            if (http.begin(url)) {
                http.addHeader("Content-Type", "application/json");
                int httpCode = http.POST(payload);
                if (httpCode == HTTP_CODE_OK) {
                    connectedToHomeServer = true;
                    WiFiClient* stream = http.getStreamPtr();

                    snprintf(ai_response_buf, sizeof(ai_response_buf), "Ty: %s\nAI: ", ai_prompt_buf);
                    int curLen = strlen(ai_response_buf);
                    ai_response_dirty = true;

                    unsigned long startWait = millis();
                    unsigned long lastUiPush = millis();

                    while ((http.connected() || stream->available() > 0) && (millis() - startWait < 15000)) {
                        server.handleClient();
                        size_t avail = stream->available();
                        if (avail > 0) {
                            char c = stream->read();
                            if ((uint8_t)c >= 32 || c == '\n') {
                                if (curLen < (int)sizeof(ai_response_buf) - 2) {
                                    ai_response_buf[curLen++] = c;
                                    ai_response_buf[curLen] = '\0';
                                }
                            }
                            startWait = millis();
                            if (millis() - lastUiPush >= 60) {
                                ai_response_dirty = true;
                                lastUiPush = millis();
                            }
                        } else {
                            vTaskDelay(pdMS_TO_TICKS(8));
                        }
                    }
                    ai_response_dirty = true;
                }
                http.end();
            }
        }
    }

    if (connectedToHomeServer) {
        syncRelaysFromServerOnCore0();
    } else {
        if (strstr(ai_prompt_buf, "Zapni") != NULL || strstr(ai_prompt_buf, "Rozsvit") != NULL || strstr(ai_prompt_buf, "rozsvit") != NULL || strstr(ai_prompt_buf, "zapni") != NULL) {
            relayStates[0] = true; relay_ui_dirty = true;
        } else if (strstr(ai_prompt_buf, "Vypni") != NULL || strstr(ai_prompt_buf, "Zhasni") != NULL || strstr(ai_prompt_buf, "zhasni") != NULL || strstr(ai_prompt_buf, "vypni") != NULL) {
            relayStates[0] = false; relay_ui_dirty = true;
        }

        char simReply[360];
        snprintf(simReply, sizeof(simReply),
            "Ty: %s\nAI [Offline Demo - Server %s:%u nedostupny]: "
            "Zkontroluj, zda na Ubuntu bezi gateway.py a zda mas v WG_ENDPOINT_ADDR spravnou IP Ubuntu serveru. "
            "Hlavni svetlo je %s.",
            ai_prompt_buf, WG_ENDPOINT_ADDR, HOME_SERVER_PORT,
            relayStates[0] ? "ZAPNUTO" : "VYPNUTO"
        );

        ai_response_buf[0] = '\0';
        int len = strlen(simReply);
        for (int i = 0; i < len; i++) {
            server.handleClient();
            int cur = strlen(ai_response_buf);
            if (cur < (int)sizeof(ai_response_buf) - 2) {
                ai_response_buf[cur] = simReply[i];
                ai_response_buf[cur + 1] = '\0';
                if (i % 6 == 0 || i == len - 1) ai_response_dirty = true;
            }
            vTaskDelay(pdMS_TO_TICKS(15));
        }
    }
    ai_is_streaming = false;
}

/* === HTML A JAVASCRIPT PRO WEBOVÝ DASHBOARD === */
const char INDEX_HTML[] PROGMEM = R"rawliteral(
<!DOCTYPE html>
<html lang="cs">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no">
<title>ESP32 Smart Hub // Control Center</title>
<style>
  :root { --bg:#0b0f17; --card:#151c28; --brd:#2a3546; --acc:#00ff88; --txt:#e6edf3; --mut:#8b949e; }
  body { background:var(--bg); color:var(--txt); font-family:system-ui,-apple-system,sans-serif; margin:0; padding:10px; text-align:center; user-select:none; }
  .top { display:flex; flex-wrap:wrap; justify-content:space-between; align-items:center; background:var(--card); border:1px solid var(--brd); border-radius:8px; padding:8px 14px; margin-bottom:10px; gap:8px; }
  .brand { font-weight:800; color:var(--acc); letter-spacing:1px; font-size:15px; }
  .sys { display:flex; flex-wrap:wrap; gap:12px; font-family:monospace; font-size:12px; color:var(--mut); }
  .sys b { color:#fff; }
  .bar { display:flex; flex-wrap:wrap; justify-content:center; gap:6px; margin-bottom:12px; }
  button, select, input { background:#21293a; color:#fff; border:1px solid var(--brd); padding:7px 12px; border-radius:6px; font-weight:600; font-size:13px; cursor:pointer; }
  button:hover { border-color:#58a6ff; }
  button:active { transform:scale(0.96); }
  .btn-act { border-color:var(--acc); box-shadow:0 0 8px rgba(0,255,136,0.35); color:var(--acc); }
  .grid { display:flex; flex-wrap:wrap; justify-content:center; gap:12px; }
  .card { background:var(--card); border:1px solid var(--brd); border-radius:10px; padding:10px; width:336px; display:flex; flex-direction:column; align-items:center; }
  .card h3 { margin:0 0 8px 0; font-size:13px; color:var(--mut); text-transform:uppercase; letter-spacing:0.5px; width:100%; display:flex; justify-content:space-between; align-items:center; }
  canvas { background:#000; border:1px solid var(--brd); border-radius:6px; touch-action:none; cursor:crosshair; }
  .row { display:flex; flex-wrap:wrap; justify-content:center; gap:6px; margin-top:8px; align-items:center; width:100%; }
  .cbtn { width:28px; height:24px; border-radius:5px; border:2px solid #555; cursor:pointer; }
  .cbtn.sel { border:3px solid var(--acc); transform:scale(1.12); }
  .dpad { display:grid; grid-template-columns:repeat(3,62px); gap:5px; justify-content:center; margin-top:6px; }
  .stat { font-size:11.5px; color:var(--mut); margin-top:6px; font-family:monospace; width:100%; text-align:left; background:#0d121a; padding:6px; border-radius:5px; box-sizing:border-box; }
  .msg-bar { max-width:1040px; margin:12px auto 0; background:var(--card); border:1px solid var(--brd); border-radius:8px; padding:10px; display:flex; flex-direction:column; gap:8px; }
  .msg-row { display:flex; gap:8px; justify-content:center; flex-wrap:wrap; }
  .ai-box { font-family:monospace; font-size:12px; color:#00ff88; background:#070a0f; border:1px solid #1e293b; border-radius:6px; padding:8px; text-align:left; white-space:pre-wrap; min-height:38px; }
</style>
</head>
<body>
  <div class="top">
    <div class="brand">ESP32 SMART HUB // WIREGUARD &amp; AI OS</div>
    <div class="sys">
      <span>Aktivni: <b id="s_app" style="color:#00ff88">MENU</b></span>
      <span>VPN: <b id="s_vpn">OFF</b></span>
      <span>Radar: <b id="s_hz">0 Hz</b></span>
      <span>RAM: <b id="s_ram">-- KB</b></span>
    </div>
  </div>

  <div class="bar">
    <button id="b_0" onclick="cmd('menu')">Menu</button>
    <button id="b_1" onclick="cmd('radar')">2D Radar</button>
    <button id="b_2" onclick="cmd('paint')">Malovani</button>
    <button id="b_3" onclick="cmd('doom')">3D Engine</button>
    <button id="b_4" onclick="cmd('home')">Smart Home</button>
    <button id="b_5" onclick="cmd('ai')">AI Agent</button>
    <button id="b_pm" onclick="cmd('mode')" style="background:#0f3a25;">Rezim: LIVE</button>
    <select id="sel_rng" onchange="setRange(this.value)">
      <option value="2000">Dosah: 2 m</option>
      <option value="4000">Dosah: 4 m</option>
      <option value="6000">Dosah: 6 m</option>
      <option value="8000" selected>Dosah: 8 m</option>
    </select>
  </div>

  <div class="grid">
    <div class="card">
      <h3><span>Radar (Klikni na cil = LOCK)</span><span id="r_lock_badge" style="color:#0ff"></span></h3>
      <canvas id="rc" width="320" height="200"></canvas>
      <div class="stat" id="r_info">Cekam na data ze senzoru...</div>
    </div>

    <div class="card">
      <h3><span>Sdilene Platno (250x240)</span><button onclick="savePng()" style="padding:2px 7px;font-size:11px;">PNG</button></h3>
      <canvas id="pc" width="250" height="240"></canvas>
      <div class="row">
        <div class="cbtn sel" id="c0" style="background:#fff" onclick="setCol(0)"></div>
        <div class="cbtn" id="c1" style="background:#f22" onclick="setCol(1)"></div>
        <div class="cbtn" id="c2" style="background:#0f2" onclick="setCol(2)"></div>
        <div class="cbtn" id="c3" style="background:#26f" onclick="setCol(3)"></div>
        <button onclick="cmd('clear')" style="background:#6e1414;padding:5px 10px;">Smazat</button>
      </div>
    </div>

    <div class="card">
      <h3><span>3D Arena &amp; Smart Relays</span><button onclick="cmd('rstcam')" style="padding:2px 7px;font-size:11px;">Kamera</button></h3>
      <canvas id="mc" width="140" height="140"></canvas>
      <div class="dpad">
        <div></div>
        <button onpointerdown="dm(1)" onpointerup="dm(0)" onpointerleave="dm(0)">W</button>
        <div></div>
        <button onpointerdown="dm(3)" onpointerup="dm(0)" onpointerleave="dm(0)">A</button>
        <button onpointerdown="dm(2)" onpointerup="dm(0)" onpointerleave="dm(0)">S</button>
        <button onpointerdown="dm(4)" onpointerup="dm(0)" onpointerleave="dm(0)">D</button>
      </div>
      <div class="row">
        <button id="rl0" onclick="tglRel(0)">Svetlo</button>
        <button id="rl1" onclick="tglRel(1)">LED</button>
        <button id="rl2" onclick="tglRel(2)">Tisk</button>
        <button id="rl3" onclick="tglRel(3)">Vetrak</button>
      </div>
      <div class="stat" id="d_info">WASD = Pohyb | Tlacitka = Rele</div>
    </div>
  </div>

  <div class="msg-bar">
    <div class="msg-row">
      <input type="text" id="msg_in" placeholder="Napis zpravu pro AI (Ollama) nebo Toast na displej..." maxlength="80" style="flex:1;max-width:520px;cursor:text;">
      <button onclick="sendAi()" style="background:#006644;">Chat s AI</button>
      <button onclick="sendMsg()" style="background:#0055aa;">Toast na displej</button>
    </div>
    <div class="ai-box" id="ai_live">AI Terminal pripraven...</div>
  </div>

<script>
const rc = document.getElementById('rc'), rctx = rc.getContext('2d');
const pc = document.getElementById('pc'), pctx = pc.getContext('2d');
const mc = document.getElementById('mc'), mctx = mc.getContext('2d');
pctx.lineCap = 'round'; pctx.lineJoin = 'round'; pctx.lineWidth = 4;

const cols = ['#ffffff','#ff2222','#00ff22','#2266ff'];
const appNames = ['MENU (Idle)','2D RADAR','MALOVANI','3D ENGINE','SMART HOME','AI AGENT','WI-FI'];
let curCol = 0, drawing = false, lx = -1, ly = -1;
let lastStrokeId = 0, lastClearId = 0;
let outStrokes = [], sendingStrokes = false;

function highlightCol(c) {
  curCol = c;
  for(let i=0;i<4;i++) document.getElementById('c'+i).className = (i===c)?'cbtn sel':'cbtn';
}
function setCol(c) { highlightCol(c); fetch('/api/cmd?a=col&c='+c); }
function cmd(a)    { fetch('/api/cmd?a='+a); }
function dm(d)     { fetch('/api/cmd?a=move&d='+d); }
function setRange(v){ fetch('/api/cmd?a=rng&v='+v); }
function tglRel(i) { fetch('/api/cmd?a=rel&i='+i); }
function savePng() {
  const a = document.createElement('a');
  a.download = 'esp32_malovani.png';
  a.href = pc.toDataURL('image/png');
  a.click();
}
function sendMsg() {
  const el = document.getElementById('msg_in');
  if(!el.value.trim()) return;
  fetch('/api/cmd?a=msg&t=' + encodeURIComponent(el.value.trim()));
  el.value = '';
}
function sendAi() {
  const el = document.getElementById('msg_in');
  if(!el.value.trim()) return;
  fetch('/api/cmd?a=aiq&t=' + encodeURIComponent(el.value.trim()));
  el.value = '';
}
document.getElementById('msg_in').addEventListener('keydown', e => {
  if(e.key === 'Enter') sendAi();
});

async function flushStrokes() {
  if(sendingStrokes || outStrokes.length === 0) return;
  sendingStrokes = true;
  while(outStrokes.length > 0) {
    const batch = outStrokes.splice(0, 12).join(';');
    try { await fetch('/api/draw?b=' + batch); } catch(e) { break; }
  }
  sendingStrokes = false;
}

function drawSeg(x1, y1, x2, y2, cIdx) {
  pctx.strokeStyle = cols[cIdx] || '#fff';
  pctx.beginPath(); pctx.moveTo(x1, y1); pctx.lineTo(x2, y2); pctx.stroke();
}
function getPos(canvas, e) {
  const r = canvas.getBoundingClientRect();
  return { x: Math.round(e.clientX - r.left), y: Math.round(e.clientY - r.top) };
}

pc.addEventListener('pointerdown', e => {
  drawing = true; const p = getPos(pc, e); lx = p.x; ly = p.y;
  drawSeg(lx, ly, lx, ly, curCol);
  outStrokes.push(`${lx+70},${ly},${lx+70},${ly},${curCol}`);
  flushStrokes();
});
pc.addEventListener('pointermove', e => {
  if(!drawing) return;
  const p = getPos(pc, e);
  if(Math.hypot(p.x - lx, p.y - ly) < 2) return;
  drawSeg(lx, ly, p.x, p.y, curCol);
  outStrokes.push(`${lx+70},${ly},${p.x+70},${p.y},${curCol}`);
  lx = p.x; ly = p.y;
  flushStrokes();
});
window.addEventListener('pointerup', () => { drawing = false; lx = -1; });

rc.addEventListener('pointerdown', e => {
  const p = getPos(rc, e);
  fetch(`/api/cmd?a=lock&x=${p.x}&y=${p.y+40}`);
});

mc.addEventListener('pointerdown', e => {
  const p = getPos(mc, e);
  const gx = Math.floor(p.x / 17.5), gy = Math.floor(p.y / 17.5);
  if(gx > 0 && gx < 7 && gy > 0 && gy < 7) {
    fetch(`/api/cmd?a=tile&x=${gx}&y=${gy}`);
  }
});

function renderRadar(d) {
  rctx.fillStyle = '#000'; rctx.fillRect(0,0,320,200);
  const cx = 160, cy = 198, rMax = 192;
  const maxMm = d.rm || 8000;

  rctx.strokeStyle = '#004400'; rctx.lineWidth = 1;
  for(let i=1;i<=4;i++) {
    let r = (rMax/4)*i;
    rctx.beginPath(); rctx.arc(cx, cy, r, Math.PI, 2*Math.PI); rctx.stroke();
    rctx.fillStyle = '#008800'; rctx.font = '10px monospace';
    let mVal = ((maxMm/1000)/4)*i;
    rctx.fillText((mVal%1===0 ? mVal : mVal.toFixed(1))+'m', cx+4, cy-r+10);
  }
  rctx.beginPath(); rctx.moveTo(cx,cy); rctx.lineTo(cx,cy-rMax); rctx.stroke();
  rctx.strokeStyle = '#00aa44';
  let x60 = rMax*0.866, y60 = rMax*0.5;
  rctx.beginPath(); rctx.moveTo(cx,cy); rctx.lineTo(cx-x60,cy-y60);
  rctx.moveTo(cx,cy); rctx.lineTo(cx+x60,cy-y60); rctx.stroke();

  if(d.app !== 1 && d.app !== 3) {
    document.getElementById('r_info').innerText = 'Radar uspan (Aktivni pouze v RADAR / 3D)';
    return;
  }

  let txt = [];
  if(d.t) {
    d.t.forEach((t, idx) => {
      if(!t.a) return;
      let px = cx - (t.x * rMax / maxMm);
      let py = cy - (t.y * rMax / maxMm);
      rctx.fillStyle = Math.abs(t.s) > 45 ? '#ff3300' : '#00ff44';
      rctx.beginPath(); rctx.arc(px, py, 6, 0, 2*Math.PI); rctx.fill();
      if(d.lk === idx) {
        rctx.strokeStyle = '#00ffff';
        rctx.strokeRect(px-11, py-11, 22, 22);
      }
      txt.push(`C${idx+1}: ${t.d}cm (${t.s}cm/s)`);
    });
  }
  document.getElementById('r_info').innerText = txt.length ? txt.join(' | ') : 'Zadny cil v zornem poli';
}

function render3DMap(d) {
  mctx.fillStyle = '#000'; mctx.fillRect(0,0,140,140);
  const bs = 17.5;
  if(d.mp && d.mp.length === 64) {
    for(let y=0;y<8;y++) {
      for(let x=0;x<8;x++) {
        let v = d.mp.charCodeAt(y*8+x) - 48;
        if(v > 0) {
          mctx.fillStyle = (v===3) ? '#00ff66' : (v===2 ? '#2266ff' : '#cc2222');
          mctx.fillRect(x*bs+1, y*bs+1, bs-2, bs-2);
        }
      }
    }
  }
  let px = d.px * bs, py = d.py * bs;
  mctx.fillStyle = '#00ffff';
  mctx.beginPath(); mctx.arc(px, py, 3.5, 0, 2*Math.PI); mctx.fill();
}

async function poll() {
  try {
    const isInitial = (lastStrokeId === 0);
    const r = await fetch('/api/state?from=' + lastStrokeId);
    const d = await r.json();

    document.getElementById('s_app').innerText = appNames[d.app] || 'MENU';
    document.getElementById('s_vpn').innerText = d.wg ? '10.8.0.50 (TUNEL OK)' : 'LAN REZIM';
    document.getElementById('s_vpn').style.color = d.wg ? '#00ff88' : '#ffaa00';
    document.getElementById('s_hz').innerText = d.hz + ' Hz';
    document.getElementById('s_ram').innerText = (d.ram / 1024).toFixed(1) + ' KB';
    if(d.ai) document.getElementById('ai_live').innerText = d.ai;

    for(let i=0;i<=5;i++) {
      const b = document.getElementById('b_'+i);
      if(b) b.className = (d.app === i) ? 'btn-act' : '';
    }
    if(d.rel) {
      for(let i=0;i<4;i++) {
        const rb = document.getElementById('rl'+i);
        if(rb) rb.className = d.rel[i] ? 'btn-act' : '';
      }
    }
    document.getElementById('b_pm').innerText = 'Rezim: ' + (d.pm ? 'PULSE' : 'LIVE');
    if(d.col !== curCol) highlightCol(d.col);

    renderRadar(d);
    render3DMap(d);

    if(d.cid !== lastClearId) {
      pctx.fillStyle = '#000'; pctx.fillRect(0,0,250,240);
      lastClearId = d.cid; lastStrokeId = 0;
    }
    if(d.st && d.st.length) {
      d.st.forEach(s => {
        if(isInitial || s[5] === 0) drawSeg(s[0]-70, s[1], s[2]-70, s[3], s[4]);
      });
    }
    lastStrokeId = d.sid;
  } catch(e) {}
  setTimeout(poll, 180);
}
poll();
</script>
</body>
</html>
)rawliteral";

/* === OBSLUHA WEBOVÝCH ENDPOINTŮ NA JÁDŘE 0 === */
void setupWebServer() {
    if (jsonBuf == NULL) {
        jsonBuf = (char*)malloc(2560);
    }

    server.on("/", HTTP_GET, []() {
        server.send_P(200, "text/html", INDEX_HTML);
    });

    server.on("/api/state", HTTP_GET, []() {
        if (jsonBuf == NULL) { server.send(500, "text/plain", "ERR"); return; }

        uint32_t fromId = 0;
        if (server.hasArg("from")) fromId = server.arg("from").toInt();

        uint32_t curTotal = (strokeHistory != NULL) ? strokeTotalCount : 0;
        uint32_t curClear = paintClearId;
        if (fromId > curTotal) fromId = curTotal;
        if (curTotal - fromId > MAX_STROKES) fromId = curTotal - MAX_STROKES;
        uint32_t toId = (curTotal - fromId > 22) ? (fromId + 22) : curTotal;

        char mapStr[65];
        int mIdx = 0;
        for (int y = 0; y < mapH; y++) {
            for (int x = 0; x < mapW; x++) {
                mapStr[mIdx++] = '0' + worldMap[y][x];
            }
        }
        mapStr[64] = '\0';

        char cleanAi[360];
        sanitizeJsonString(cleanAi, ai_response_buf, sizeof(cleanAi));

        int pos = 0;
        pos += snprintf(jsonBuf + pos, 2560 - pos,
            "{\"app\":%d,\"wg\":%d,\"pm\":%d,\"hm\":%d,\"rm\":%d,\"col\":%d,\"lk\":%d,\"aim\":%d,"
            "\"px\":%.2f,\"py\":%.2f,\"pa\":%.2f,\"pr\":%d,"
            "\"ram\":%u,\"rssi\":%d,\"up\":%lu,\"hz\":%d,"
            "\"cid\":%u,\"sid\":%u,\"rel\":[%d,%d,%d,%d],\"mp\":\"%s\",\"ai\":\"%s\",\"t\":[",
            (int)activeApp,
            wg_connected ? 1 : 0,
            radar_pulse_mode ? 1 : 0,
            radar_multi_mode ? 1 : 0,
            current_max_y_mm,
            (int)colorToIndex(paint_color),
            locked_target_idx,
            aimedTargetGlobal,
            playerX, playerY, playerAngle,
            (int)pulseRadius,
            ESP.getFreeHeap(),
            (int)WiFi.RSSI(),
            millis() / 1000UL,
            radar_fps,
            curClear, toId,
            relayStates[0]?1:0, relayStates[1]?1:0, relayStates[2]?1:0, relayStates[3]?1:0,
            mapStr, cleanAi
        );

        for (int i = 0; i < 3; i++) {
            bool act = (activeApp == APP_RADAR || activeApp == APP_DOOM) &&
                       targets[i].active && (millis() - targets[i].lastTime < KEEPALIVE_MS);
            pos += snprintf(jsonBuf + pos, 2560 - pos,
                "%s{\"a\":%d,\"x\":%d,\"y\":%d,\"d\":%d,\"s\":%d,\"g\":%u,\"ang\":%.0f,\"vx\":%.1f,\"vy\":%.1f}",
                (i > 0) ? "," : "",
                act ? 1 : 0,
                (int)targets[i].raw_x, (int)targets[i].raw_y,
                (int)targets[i].dist, (int)targets[i].speed,
                targets[i].gate_res_mm, targets[i].angle_deg,
                targets[i].velX, targets[i].velY
            );
        }

        pos += snprintf(jsonBuf + pos, 2560 - pos, "],\"st\":[");
        if (strokeHistory != NULL) {
            for (uint32_t s = fromId; s < toId; s++) {
                StrokeSegment seg = strokeHistory[s % MAX_STROKES];
                uint8_t cIdx = seg.flags & 0x03;
                uint8_t isWeb = (seg.flags & 0x04) ? 1 : 0;
                pos += snprintf(jsonBuf + pos, 2560 - pos,
                    "%s[%u,%u,%u,%u,%u,%u]",
                    (s > fromId) ? "," : "",
                    seg.x1, seg.y1, seg.x2, seg.y2, cIdx, isWeb
                );
            }
        }
        snprintf(jsonBuf + pos, 2560 - pos, "]}");

        server.send(200, "application/json", jsonBuf);
    });

    server.on("/api/draw", HTTP_GET, []() {
        if (activeApp != APP_PAINT) {
            remote_cmd = 3; 
        }
        if (server.hasArg("b") && strokeHistory != NULL && webDrawQ != NULL) {
            String batch = server.arg("b");
            int start = 0;
            while (start < (int)batch.length()) {
                int end = batch.indexOf(';', start);
                if (end == -1) end = batch.length();
                String item = batch.substring(start, end);
                int x1, y1, x2, y2, c;
                if (sscanf(item.c_str(), "%d,%d,%d,%d,%d", &x1, &y1, &x2, &y2, &c) == 5) {
                    recordStroke(x1, y1, x2, y2, (uint8_t)c, true);
                    int nextHead = (webDrawHead + 1) % WEB_DRAW_Q_SIZE;
                    if (nextHead != webDrawTail) {
                        webDrawQ[webDrawHead].x1 = constrain(x1, 74, 319);
                        webDrawQ[webDrawHead].y1 = constrain(y1, 0, 239);
                        webDrawQ[webDrawHead].x2 = constrain(x2, 74, 319);
                        webDrawQ[webDrawHead].y2 = constrain(y2, 0, 239);
                        webDrawQ[webDrawHead].flags = (uint8_t)(c & 0x03);
                        webDrawHead = nextHead;
                    }
                }
                start = end + 1;
            }
        }
        server.send(200, "text/plain", "OK");
    });

    server.on("/api/cmd", HTTP_GET, []() {
        String a = server.arg("a");
        if (a == "menu")        remote_cmd = 1;
        else if (a == "radar")  remote_cmd = 2;
        else if (a == "paint")  remote_cmd = 3;
        else if (a == "doom")   remote_cmd = 4;
        else if (a == "mode")   remote_cmd = 5;
        else if (a == "clear")  remote_cmd = 6;
        else if (a == "hw1")    remote_cmd = 7;
        else if (a == "hw3")    remote_cmd = 8;
        else if (a == "rstcam") remote_cmd = 9;
        else if (a == "home")   remote_cmd = 11;
        else if (a == "ai")     remote_cmd = 12;
        else if (a == "col") {
            uint8_t c = server.arg("c").toInt();
            paint_color = indexToColor(c);
            paint_ui_dirty = true;
        } else if (a == "move") {
            web_doom_action = server.arg("d").toInt();
        } else if (a == "rng") {
            int v = constrain(server.arg("v").toInt(), 2000, 8000);
            current_max_y_mm = v;
            if (activeApp == APP_RADAR) remote_cmd = 10; 
        } else if (a == "lock") {
            web_lock_req_x = server.arg("x").toInt();
            web_lock_req_y = server.arg("y").toInt();
        } else if (a == "rel") {
            pending_relay_toggle = constrain(server.arg("i").toInt(), 0, RELAY_COUNT - 1);
        } else if (a == "aiq") {
            String t = server.arg("t");
            if (t.length() > 0 && !ai_is_streaming) {
                strncpy(ai_prompt_buf, t.c_str(), sizeof(ai_prompt_buf) - 1);
                ai_prompt_buf[sizeof(ai_prompt_buf) - 1] = '\0';
                if (activeApp != APP_AI) remote_cmd = 12;
                ai_request_pending = true;
            }
        } else if (a == "tile") {
            int gx = server.arg("x").toInt();
            int gy = server.arg("y").toInt();
            if (gx > 0 && gx < mapW - 1 && gy > 0 && gy < mapH - 1) {
                if ((int)playerX != gx || (int)playerY != gy) {
                    worldMap[gy][gx] = (worldMap[gy][gx] + 1) % 3;
                }
            }
        } else if (a == "msg") {
            String t = server.arg("t");
            if (t.length() > 0) {
                strncpy(remote_toast_text, t.c_str(), sizeof(remote_toast_text) - 1);
                remote_toast_text[sizeof(remote_toast_text) - 1] = '\0';
                remote_toast_pending = true;
            }
        }
        server.send(200, "text/plain", "OK");
    });

    server.begin();
}

/* === BEZPEČNÁ OBSLUHA WIREGUARDU (NEKRADE DEFAULT ROUTE PRO MOBIL NA WI-FI!) === */
static struct netif* saved_wifi_netif = NULL;

void stopWireGuardSafely() {
    if (wg_connected && wg.is_initialized()) {
        #ifdef LOCK_TCPIP_CORE
        LOCK_TCPIP_CORE();
        #endif
        wg.end();
        if (saved_wifi_netif != NULL) {
            netif_set_default(saved_wifi_netif);
        }
        #ifdef UNLOCK_TCPIP_CORE
        UNLOCK_TCPIP_CORE();
        #endif
    }
    wg_connected = false;
}

bool isWireGuardKeyConfigured() {
    return (strlen(WG_PRIVATE_KEY) >= 40 &&
            strstr(WG_PRIVATE_KEY, "SEM_VLOZ") == NULL &&
            strlen(WG_PUBLIC_KEY) >= 40 &&
            strstr(WG_PUBLIC_KEY, "SEM_VLOZ") == NULL);
}

void activateWireGuardNonBlocking() {
    if (!isWireGuardKeyConfigured() || wg.is_initialized()) return;

    #ifdef LOCK_TCPIP_CORE
    LOCK_TCPIP_CORE();
    #endif
    saved_wifi_netif = netif_default;

    wg.begin(WG_LOCAL_IP, WG_PRIVATE_KEY, WG_ENDPOINT_ADDR, WG_PUBLIC_KEY, WG_ENDPOINT_PORT);

    struct netif* wg_netif = netif_default;
    if (wg_netif != NULL && wg_netif != saved_wifi_netif) {
        ip4_addr_t wg_mask;
        IP4_ADDR(&wg_mask, 255, 255, 255, 0);
        netif_set_netmask(wg_netif, &wg_mask);
        if (saved_wifi_netif != NULL) {
            netif_set_default(saved_wifi_netif);
        }
    }
    #ifdef UNLOCK_TCPIP_CORE
    UNLOCK_TCPIP_CORE();
    #endif

    wg_connected = true;
    String ipStr = WiFi.localIP().toString();
    snprintf(wifi_ip_str, sizeof(wifi_ip_str), "%s | WG", ipStr.c_str());
    snprintf(lan_status_detail, sizeof(lan_status_detail), "LAN IP: %s | VPN: 10.8.0.50", ipStr.c_str());
    status_bar_dirty = true;
}

/* === FREERTOS TASK PRO SÍŤ, WIREGUARD, AI STREAMING A SMART HOME (Jádro 0) === */
void networkTask(void * pvParameters) {
    unsigned long last_connect_attempt = 0;
    const unsigned long CONNECT_TIMEOUT = 12000; 
    bool scanning_in_progress = false;
    bool server_started = false;
    bool wg_waiting_for_ntp = false;
    bool initial_relay_sync_done = false;
    unsigned long ntp_start_ms = 0;
    
    while (true) {
        if (wifi_connected && server_started) {
            server.handleClient();
        }

        if (pending_relay_toggle >= 0) {
            int idx = pending_relay_toggle;
            pending_relay_toggle = -1;
            executeSmartHomeRelayOnCore0(idx);
        }

        if (ai_request_pending) {
            ai_request_pending = false;
            executeAIStreamOnCore0();
        }

        // OPRAVA: Skenování Wi-Fi neshodí existující připojení, pokud už jsme připojeni!
        if (wifi_scan_request) {
            wifi_scan_request = false;
            if (WiFi.status() != WL_CONNECTED) {
                WiFi.disconnect();
                vTaskDelay(pdMS_TO_TICKS(80));
            }
            WiFi.scanNetworks(true); 
            scanning_in_progress = true;
        }

        if (scanning_in_progress) {
            if (activeApp != APP_WIFI) {
                WiFi.scanDelete();
                scanning_in_progress = false;
            } else {
                int n = WiFi.scanComplete();
                if (n >= 0) {
                    String opts = "";
                    int limit = (n > 12) ? 12 : n;
                    for (int i = 0; i < limit; ++i) {
                        opts += WiFi.SSID(i);
                        if (i < limit - 1) opts += "\n";
                    }
                    if (opts.length() == 0) opts = "Zadne site v okoli";
                    strncpy(scan_options_buf, opts.c_str(), sizeof(scan_options_buf) - 1);
                    scan_options_buf[sizeof(scan_options_buf) - 1] = '\0';
                    
                    WiFi.scanDelete();
                    scanning_in_progress = false;
                    wifi_scan_ready = true;
                } else if (n == WIFI_SCAN_FAILED) {
                    scanning_in_progress = false;
                }
            }
        }

        if (wifi_connect_request) {
            wifi_connect_request = false;
            stopWireGuardSafely();
            wg_waiting_for_ntp = false;
            wifi_connected = false;
            snprintf(wifi_ip_str, sizeof(wifi_ip_str), "Pripojuji...");
            snprintf(lan_status_detail, sizeof(lan_status_detail), "Pripojuji k: %s...", current_ssid);
            status_bar_dirty = true;

            WiFi.disconnect();
            vTaskDelay(pdMS_TO_TICKS(100)); 
            WiFi.mode(WIFI_STA);
            if (strlen(current_ssid) > 0) {
                Serial.printf("[WIFI] Pripojuji k SSID: %s\n", current_ssid);
                WiFi.begin(current_ssid, current_pass);
                last_connect_attempt = millis(); 
            }
        }

        if (WiFi.status() == WL_CONNECTED) {
            if (!wifi_connected) {
                String ipStr = WiFi.localIP().toString();
                Serial.printf("[WIFI] PRIPOJENO! Lokalni IP adresa: http://%s\n", ipStr.c_str());

                snprintf(wifi_ip_str, sizeof(wifi_ip_str), "IP: %s", ipStr.c_str());
                snprintf(lan_status_detail, sizeof(lan_status_detail), "LAN IP: http://%s", ipStr.c_str());
                wifi_connected = true;
                status_bar_dirty = true;

                if (!server_started) {
                    setupWebServer();
                    server_started = true;
                }

                if (isWireGuardKeyConfigured()) {
                    configTime(3600, 3600, "pool.ntp.org", "time.google.com");
                    wg_waiting_for_ntp = true;
                    ntp_start_ms = millis();
                }
                initial_relay_sync_done = false;
            }

            if (wg_waiting_for_ntp) {
                time_t nowEpoch = time(nullptr);
                if (nowEpoch > 1700000000 || (millis() - ntp_start_ms > 3500)) {
                    wg_waiting_for_ntp = false;
                    activateWireGuardNonBlocking();
                }
            }

            if (!initial_relay_sync_done && !wg_waiting_for_ntp) {
                initial_relay_sync_done = true;
                syncRelaysFromServerOnCore0();
            }

            server.handleClient();
            vTaskDelay(pdMS_TO_TICKS(5));
        } else {
            if (wifi_connected) {
                stopWireGuardSafely();
                wg_waiting_for_ntp = false;
                wifi_connected = false;
                snprintf(wifi_ip_str, sizeof(wifi_ip_str), "Wi-Fi: OFF");
                snprintf(lan_status_detail, sizeof(lan_status_detail), "Odpojeno (Zkontroluj Wi-Fi)");
                status_bar_dirty = true;
            }
            if (strlen(current_ssid) > 0 && !wifi_connect_request && !scanning_in_progress) {
                if (millis() - last_connect_attempt > CONNECT_TIMEOUT) {
                    snprintf(wifi_ip_str, sizeof(wifi_ip_str), "Pripojuji...");
                    status_bar_dirty = true;
                    WiFi.disconnect();
                    vTaskDelay(pdMS_TO_TICKS(100));
                    WiFi.begin(current_ssid, current_pass);
                    last_connect_attempt = millis(); 
                }
            }
            vTaskDelay(pdMS_TO_TICKS(200)); 
        }
    }
}

/* === OVLADAČE LVGL === */
void my_disp_flush(lv_disp_drv_t *disp_drv, const lv_area_t *area, lv_color_t *color_p) {
    uint32_t w = (area->x2 - area->x1 + 1);
    uint32_t h = (area->y2 - area->y1 + 1);
    tft.pushImage(area->x1, area->y1, w, h, (uint16_t *)&color_p->full);
    lv_disp_flush_ready(disp_drv);
}

void my_touchpad_read(lv_indev_drv_t * indev_drv, lv_indev_data_t * data) {
    uint16_t touchX, touchY;
    bool touched = tft.getTouch(&touchX, &touchY, 600);
    if (!touched) {
        data->state = LV_INDEV_STATE_REL;
    } else {
        data->state = LV_INDEV_STATE_PR;
        data->point.x = touchX;
        data->point.y = touchY;
    }
}

uint16_t getSpeedColor(float speed) {
    int s = constrain((int)speed, 0, MAX_SPEED_CMS);
    uint8_t r = 0, g = 0, b = 0; 
    if (s < (MAX_SPEED_CMS / 2)) {
        r = map(s, 0, MAX_SPEED_CMS / 2, 0, 255);
        g = 255;
    } else {
        r = 255;
        g = map(s, MAX_SPEED_CMS / 2, MAX_SPEED_CMS, 255, 0);
    }
    return tft.color565(r, g, b); 
}

/* === HARD-OFF SPRÁVCE ŽIVOTNÍHO CYKLU APLIKACÍ === */
void create_launcher_screen();
void create_radar_screen();
void create_paint_screen();
void create_doom_screen();
void create_home_screen();
void create_ai_screen();
void create_wifi_screen();

void shutdownCurrentApp() {
    if (zBuffer != NULL) { free(zBuffer); zBuffer = NULL; }
    if (echos != NULL)   { free(echos);   echos = NULL; }

    is_drawing = false;
    last_drawn_x = -1;
    last_drawn_y = -1;
    paint_needs_restore = false;
    doom_action = 0;
    web_doom_action = 0;

    launcher_ip_label = NULL;
    btn_mode_label = NULL;
    kb = NULL;
    dd_ssid = NULL;
    ta_pass = NULL;
    ai_ta_out = NULL;
    ai_ta_in = NULL;
    ai_btn_send = NULL;
    for (int i = 0; i < 4; i++) {
        color_btns[i] = NULL;
        relay_btns[i] = NULL;
        relay_lbls[i] = NULL;
        ai_qbtns[i] = NULL;
    }
    for (int i = 0; i < 3; i++) {
        targets[i].active = false;
        targets[i].lastR = 0;
        targets[i].trailCount = 0;
        targets[i].lastTrailCount = 0;
    }
}

void launchApp(AppID newApp) {
    shutdownCurrentApp();
    activeApp = newApp;

    if (newApp == APP_RADAR) {
        echos = (PulseEcho*)calloc(MAX_ECHOS, sizeof(PulseEcho));
        while (Serial2.available()) Serial2.read();
        parserState = HEAD1;
    } else if (newApp == APP_DOOM) {
        zBuffer = (float*)malloc(80 * sizeof(float));
        while (Serial2.available()) Serial2.read();
        parserState = HEAD1;
    } else {
        radar_fps = 0;
        radar_frame_counter = 0;
    }

    bool showWifiBadge = (newApp == APP_LAUNCHER || newApp == APP_WIFI);
    if (showWifiBadge) lv_obj_clear_flag(wifi_icon, LV_OBJ_FLAG_HIDDEN);
    else               lv_obj_add_flag(wifi_icon, LV_OBJ_FLAG_HIDDEN);

    lv_obj_t * old_scr = lv_scr_act();
    current_screen = lv_obj_create(NULL);
    lv_obj_clear_flag(current_screen, LV_OBJ_FLAG_SCROLLABLE);

    switch (newApp) {
        case APP_LAUNCHER: create_launcher_screen(); break;
        case APP_RADAR:    create_radar_screen();    break;
        case APP_PAINT:    create_paint_screen();    break;
        case APP_DOOM:     create_doom_screen();     break;
        case APP_HOME:     create_home_screen();     break;
        case APP_AI:       create_ai_screen();       break;
        case APP_WIFI:     
            create_wifi_screen();
            wifi_scan_ready = false;
            wifi_scan_request = true;
            break;
    }

    status_bar_dirty = true;
    lv_scr_load(current_screen);
    if (old_scr != NULL && old_scr != current_screen) {
        lv_obj_del(old_scr);
    }
    lv_refr_now(NULL);
}

/* === EVENT HANDLERY === */
static void btn_back_cb(lv_event_t * e) { launchApp(APP_LAUNCHER); }

static void btn_mode_cb(lv_event_t * e) {
    radar_pulse_mode = !radar_pulse_mode; 
    if (activeApp == APP_RADAR && btn_mode_label != NULL) {
        lv_label_set_text(btn_mode_label, radar_pulse_mode ? "PULSE" : "LIVE");
        lv_refr_now(NULL);
        tft.fillRect(0, 42, screenWidth, screenHeight - 42, RADAR_BG);
    }
    for (int i = 0; i < 3; i++) { 
        targets[i].lastR = 0; 
        targets[i].lastGateR = 0;
        targets[i].hadVec = false;
        targets[i].hadLockBox = false;
        targets[i].lastTrailCount = 0;
    }
    if (echos != NULL) {
        for (int i = 0; i < MAX_ECHOS; i++) { 
            echos[i].active = false; 
            echos[i].life = 0; 
            echos[i].lastR = 0; 
        }
    }
    pulseRadius = 0; 
    lastPulseRadius = 0;
    radar_needs_grid = true;
}

void performTargetLockAt(int px, int py) {
    if (py < 42) return;
    int bestIdx = -1;
    float bestDist = 38.0f;

    for (int i = 0; i < 3; i++) {
        if (targets[i].active) {
            float dx = (float)px - targets[i].smoothX;
            float dy = (float)py - targets[i].smoothY;
            float d = sqrtf(dx * dx + dy * dy);
            if (d < bestDist) {
                bestDist = d;
                bestIdx = i;
            }
        }
    }

    if (locked_target_idx != bestIdx) {
        locked_target_idx = bestIdx;
        if (activeApp == APP_RADAR) {
            tft.fillRect(0, 44, 105, 50, RADAR_BG);
            tft.fillRect(236, 44, 84, 65, RADAR_BG);
            radar_needs_grid = true;
        }
    }
}

static void radar_touch_cb(lv_event_t * e) {
    if (radar_pulse_mode) return; 
    lv_indev_t * indev = lv_indev_get_act();
    if (!indev) return;
    lv_point_t p;
    lv_indev_get_point(indev, &p);
    performTargetLockAt(p.x, p.y);
}

void clearPaintCanvas() {
    strokeTotalCount = 0;
    paintClearId++;
    webDrawHead = 0;
    webDrawTail = 0;
    if (activeApp == APP_PAINT) {
        tft.fillRect(70, 0, 250, 240, TFT_BLACK);
    }
}

static void paint_clear_cb(lv_event_t * e) { clearPaintCanvas(); }

void updatePaintColorButtonsUI() {
    if (activeApp != APP_PAINT) return;
    uint16_t colors[] = {TFT_WHITE, TFT_RED, TFT_GREEN, TFT_BLUE};
    for (int i = 0; i < 4; i++) {
        if (color_btns[i] != NULL) {
            lv_obj_set_style_border_width(color_btns[i], (paint_color == colors[i]) ? 3 : 1, 0);
        }
    }
}

static void paint_color_cb(lv_event_t * e) { 
    paint_color = (uint16_t)(size_t)lv_event_get_user_data(e); 
    updatePaintColorButtonsUI();
}

static void paint_draw_cb(lv_event_t * e) {
    lv_event_code_t code = lv_event_get_code(e);
    lv_indev_t * indev = lv_indev_get_act();
    if (!indev) return;
    lv_point_t p;
    lv_indev_get_point(indev, &p);
    if (p.x < 74) { is_drawing = false; last_drawn_x = -1; last_drawn_y = -1; return; }
    if (code == LV_EVENT_PRESSED || code == LV_EVENT_PRESSING) {
        paint_x = p.x; paint_y = p.y; is_drawing = true;
    } else if (code == LV_EVENT_RELEASED || code == LV_EVENT_PRESS_LOST) {
        is_drawing = false; last_drawn_x = -1; last_drawn_y = -1;
    }
}

static void doom_touch_cb(lv_event_t * e) {
    lv_event_code_t code = lv_event_get_code(e);
    lv_indev_t * indev = lv_indev_get_act();
    if (!indev) return;
    lv_point_t p;
    lv_indev_get_point(indev, &p);

    if (p.y < VIEW_TOP) { doom_action = 0; return; } 

    if (code == LV_EVENT_PRESSED || code == LV_EVENT_PRESSING) {
        if (p.x < 90) doom_action = 3;       
        else if (p.x > 230) doom_action = 4; 
        else if (p.y < 135) doom_action = 1; 
        else doom_action = 2;                
    } else if (code == LV_EVENT_RELEASED || code == LV_EVENT_PRESS_LOST) {
        doom_action = 0;
    }
}

/* === APLIKACE 1: HUB LAUNCHER (6 IKON + DOLNÍ INFORMAČNÍ LIŠTA S IP ADRESOU) === */
void create_launcher_screen() {
    lv_obj_set_style_bg_color(current_screen, lv_color_hex(0x12161f), 0);
    lv_obj_t * title = lv_label_create(current_screen);
    lv_label_set_text(title, "SMART HUB OS");
    lv_obj_align(title, LV_ALIGN_TOP_LEFT, 10, 6);
    lv_obj_set_style_text_color(title, lv_color_hex(0x00FF88), 0);

    const char* labels[6] = {"RADAR", "MALOVANI", "3D engine", "SMART HOME", "AI AGENT", "Wi-Fi"};
    const uint32_t colors[6] = {0x0055cc, 0x8A2BE2, 0x228B22, 0xD97706, 0x0D9488, 0x3B4252};
    const AppID apps[6] = {APP_RADAR, APP_PAINT, APP_DOOM, APP_HOME, APP_AI, APP_WIFI};

    for (int i = 0; i < 6; i++) {
        int col = i % 3;
        int row = i / 3;
        lv_obj_t * btn = lv_btn_create(current_screen);
        lv_obj_set_size(btn, 96, 78);
        lv_obj_align(btn, LV_ALIGN_TOP_LEFT, 10 + col * 102, 28 + row * 84);
        lv_obj_set_style_bg_color(btn, lv_color_hex(colors[i]), 0);
        lv_obj_add_event_cb(btn, [](lv_event_t * e) {
            AppID targetApp = (AppID)(size_t)lv_event_get_user_data(e);
            launchApp(targetApp);
        }, LV_EVENT_CLICKED, (void*)(size_t)apps[i]);

        lv_obj_t * lbl = lv_label_create(btn);
        lv_label_set_text(lbl, labels[i]);
        lv_obj_center(lbl);
    }

    // Dolní informační panel s plnou lokální IP adresou pro mobil a stavem VPN
    lv_obj_t * ip_bar = lv_obj_create(current_screen);
    lv_obj_set_size(ip_bar, 304, 24);
    lv_obj_align(ip_bar, LV_ALIGN_BOTTOM_MID, 0, -4);
    lv_obj_set_style_bg_color(ip_bar, lv_color_hex(0x090d14), 0);
    lv_obj_set_style_border_color(ip_bar, lv_color_hex(0x2a3546), 0);
    lv_obj_set_style_border_width(ip_bar, 1, 0);
    lv_obj_clear_flag(ip_bar, LV_OBJ_FLAG_SCROLLABLE);

    launcher_ip_label = lv_label_create(ip_bar);
    lv_label_set_text(launcher_ip_label, lan_status_detail);
    lv_obj_set_style_text_color(launcher_ip_label, lv_color_hex(wifi_connected ? 0x00FF88 : 0xFFAA00), 0);
    lv_obj_center(launcher_ip_label);
}

/* === APLIKACE 5: SMART HOME OVLÁDÁNÍ RELÉ === */
void updateSmartHomeUI() {
    if (activeApp != APP_HOME) return;
    for (int i = 0; i < RELAY_COUNT; i++) {
        if (relay_btns[i] != NULL && relay_lbls[i] != NULL) {
            bool st = relayStates[i];
            lv_obj_set_style_bg_color(relay_btns[i], lv_color_hex(st ? 0x16A34A : 0x27303F), 0);
            lv_obj_set_style_border_color(relay_btns[i], lv_color_hex(st ? 0x4ADE80 : 0x4B5563), 0);
            lv_label_set_text_fmt(relay_lbls[i], "%s\n[%s]", relayNames[i], st ? "ZAPNUTO" : "VYPNUTO");
        }
    }
}

void create_home_screen() {
    lv_obj_set_style_bg_color(current_screen, lv_color_hex(0x0f141c), 0);

    lv_obj_t * btn_back = lv_btn_create(current_screen);
    lv_obj_set_size(btn_back, 65, 32);
    lv_obj_align(btn_back, LV_ALIGN_TOP_LEFT, 6, 5);
    lv_obj_set_style_bg_color(btn_back, lv_color_hex(0xAA0000), 0);
    lv_obj_add_event_cb(btn_back, btn_back_cb, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_back = lv_label_create(btn_back);
    lv_label_set_text(lbl_back, "ZPET");
    lv_obj_center(lbl_back);

    lv_obj_t * title = lv_label_create(current_screen);
    lv_label_set_text(title, "SMART HOME RELE");
    lv_obj_align(title, LV_ALIGN_TOP_MID, 25, 12);
    lv_obj_set_style_text_color(title, lv_color_hex(0xFBBF24), 0);

    for (int i = 0; i < RELAY_COUNT; i++) {
        int col = i % 2;
        int row = i / 2;
        relay_btns[i] = lv_btn_create(current_screen);
        lv_obj_set_size(relay_btns[i], 146, 84);
        lv_obj_align(relay_btns[i], LV_ALIGN_TOP_LEFT, 8 + col * 156, 46 + row * 92);
        lv_obj_set_style_border_width(relay_btns[i], 2, 0);
        lv_obj_add_event_cb(relay_btns[i], [](lv_event_t * e) {
            int idx = (int)(size_t)lv_event_get_user_data(e);
            pending_relay_toggle = idx;
        }, LV_EVENT_CLICKED, (void*)(size_t)i);

        relay_lbls[i] = lv_label_create(relay_btns[i]);
        lv_obj_set_style_text_align(relay_lbls[i], LV_TEXT_ALIGN_CENTER, 0);
        lv_obj_center(relay_lbls[i]);
    }
    updateSmartHomeUI();
}

/* === APLIKACE 6: LOKÁLNÍ AI CHAT S VYSKAKOVACÍ KLÁVESNICÍ === */
void triggerAIPrompt(const char* promptText) {
    if (ai_is_streaming || promptText == NULL || strlen(promptText) == 0) return;
    strncpy(ai_prompt_buf, promptText, sizeof(ai_prompt_buf) - 1);
    ai_prompt_buf[sizeof(ai_prompt_buf) - 1] = '\0';
    ai_request_pending = true;
}

void setAIKeyboardVisible(bool visible) {
    if (activeApp != APP_AI || kb == NULL || ai_ta_out == NULL || ai_ta_in == NULL) return;

    if (visible) {
        lv_obj_set_size(ai_ta_out, 312, 54);
        lv_obj_align(ai_ta_out, LV_ALIGN_TOP_MID, 0, 34);

        lv_obj_set_size(ai_ta_in, 232, 32);
        lv_obj_align(ai_ta_in, LV_ALIGN_TOP_LEFT, 4, 91);

        if (ai_btn_send != NULL) {
            lv_obj_align(ai_btn_send, LV_ALIGN_TOP_RIGHT, -4, 91);
            lv_obj_clear_flag(ai_btn_send, LV_OBJ_FLAG_HIDDEN);
        }
        for (int i = 0; i < 4; i++) {
            if (ai_qbtns[i] != NULL) lv_obj_add_flag(ai_qbtns[i], LV_OBJ_FLAG_HIDDEN);
        }

        lv_obj_clear_flag(kb, LV_OBJ_FLAG_HIDDEN);
        lv_obj_move_foreground(kb);
    } else {
        lv_obj_add_flag(kb, LV_OBJ_FLAG_HIDDEN);

        lv_obj_set_size(ai_ta_out, 312, 116);
        lv_obj_align(ai_ta_out, LV_ALIGN_TOP_MID, 0, 34);

        lv_obj_set_size(ai_ta_in, 232, 32);
        lv_obj_align(ai_ta_in, LV_ALIGN_TOP_LEFT, 4, 154);

        if (ai_btn_send != NULL) {
            lv_obj_align(ai_btn_send, LV_ALIGN_TOP_RIGHT, -4, 154);
            lv_obj_clear_flag(ai_btn_send, LV_OBJ_FLAG_HIDDEN);
        }
        for (int i = 0; i < 4; i++) {
            if (ai_qbtns[i] != NULL) lv_obj_clear_flag(ai_qbtns[i], LV_OBJ_FLAG_HIDDEN);
        }
    }
}

void submitTypedAIPrompt() {
    if (ai_ta_in == NULL) return;
    const char* txt = lv_textarea_get_text(ai_ta_in);
    if (txt != NULL && strlen(txt) > 0) {
        triggerAIPrompt(txt);
        lv_textarea_set_text(ai_ta_in, "");
    }
    setAIKeyboardVisible(false);
}

static void ai_ta_in_event_cb(lv_event_t * e) {
    lv_event_code_t code = lv_event_get_code(e);
    if (code == LV_EVENT_CLICKED || code == LV_EVENT_PRESSED) {
        setAIKeyboardVisible(true);
    }
}

static void ai_kb_event_cb(lv_event_t * e) {
    lv_event_code_t code = lv_event_get_code(e);
    if (code == LV_EVENT_READY) {
        submitTypedAIPrompt();
    } else if (code == LV_EVENT_CANCEL) {
        setAIKeyboardVisible(false);
    }
}

void create_ai_screen() {
    lv_obj_set_style_bg_color(current_screen, lv_color_hex(0x0b131e), 0);

    lv_obj_t * btn_back = lv_btn_create(current_screen);
    lv_obj_set_size(btn_back, 58, 28);
    lv_obj_align(btn_back, LV_ALIGN_TOP_LEFT, 4, 3);
    lv_obj_set_style_bg_color(btn_back, lv_color_hex(0xAA0000), 0);
    lv_obj_add_event_cb(btn_back, btn_back_cb, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_back = lv_label_create(btn_back);
    lv_label_set_text(lbl_back, "ZPET");
    lv_obj_center(lbl_back);

    lv_obj_t * title = lv_label_create(current_screen);
    lv_label_set_text(title, "AI CHAT (OLLAMA)");
    lv_obj_align(title, LV_ALIGN_TOP_MID, 0, 9);
    lv_obj_set_style_text_color(title, lv_color_hex(0x2DD4BF), 0);

    lv_obj_t * btn_clr = lv_btn_create(current_screen);
    lv_obj_set_size(btn_clr, 52, 28);
    lv_obj_align(btn_clr, LV_ALIGN_TOP_RIGHT, -4, 3);
    lv_obj_set_style_bg_color(btn_clr, lv_color_hex(0x334155), 0);
    lv_obj_add_event_cb(btn_clr, [](lv_event_t * e) {
        snprintf(ai_response_buf, sizeof(ai_response_buf), "Konverzace vycistena.\nTapni do pole dole pro klavesnici.");
        if (ai_ta_out != NULL) lv_textarea_set_text(ai_ta_out, ai_response_buf);
    }, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_clr = lv_label_create(btn_clr);
    lv_label_set_text(lbl_clr, "CLR");
    lv_obj_center(lbl_clr);

    ai_ta_out = lv_textarea_create(current_screen);
    lv_obj_set_size(ai_ta_out, 312, 116);
    lv_obj_align(ai_ta_out, LV_ALIGN_TOP_MID, 0, 34);
    lv_obj_set_style_bg_color(ai_ta_out, lv_color_hex(0x05080d), 0);
    lv_obj_set_style_text_color(ai_ta_out, lv_color_hex(0x00FF88), 0);
    lv_obj_set_style_border_color(ai_ta_out, lv_color_hex(0x1E293B), 0);
    lv_textarea_set_cursor_click_pos(ai_ta_out, false);
    lv_textarea_set_text(ai_ta_out, ai_response_buf);

    ai_ta_in = lv_textarea_create(current_screen);
    lv_textarea_set_one_line(ai_ta_in, true);
    lv_obj_set_size(ai_ta_in, 232, 32);
    lv_obj_align(ai_ta_in, LV_ALIGN_TOP_LEFT, 4, 154);
    lv_obj_set_style_bg_color(ai_ta_in, lv_color_hex(0x162032), 0);
    lv_obj_set_style_text_color(ai_ta_in, lv_color_hex(0xFFFFFF), 0);
    lv_obj_set_style_border_color(ai_ta_in, lv_color_hex(0x0D9488), 0);
    lv_textarea_set_placeholder_text(ai_ta_in, "Napis zpravu pro AI...");
    lv_obj_add_event_cb(ai_ta_in, ai_ta_in_event_cb, LV_EVENT_ALL, NULL);

    ai_btn_send = lv_btn_create(current_screen);
    lv_obj_set_size(ai_btn_send, 74, 32);
    lv_obj_align(ai_btn_send, LV_ALIGN_TOP_RIGHT, -4, 154);
    lv_obj_set_style_bg_color(ai_btn_send, lv_color_hex(0x0D9488), 0);
    lv_obj_add_event_cb(ai_btn_send, [](lv_event_t * e) {
        submitTypedAIPrompt();
    }, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_send = lv_label_create(ai_btn_send);
    lv_label_set_text(lbl_send, "POSLAT");
    lv_obj_center(lbl_send);

    const char* qLabels[4] = {"Stav", "Rozsvit", "Zhasni", "Tip"};
    const char* qPrompts[4] = {
        "Shrn stav chytrych zarizeni v dome.",
        "Zapni hlavni svetlo v pokoji a potvrd to.",
        "Vypni hlavni svetlo v pokoji a potvrd to.",
        "Rekni kratkou technickou zajímavost o mmWave radaru."
    };

    for (int i = 0; i < 4; i++) {
        ai_qbtns[i] = lv_btn_create(current_screen);
        lv_obj_set_size(ai_qbtns[i], 73, 42);
        lv_obj_align(ai_qbtns[i], LV_ALIGN_BOTTOM_LEFT, 5 + i * 78, -5);
        lv_obj_set_style_bg_color(ai_qbtns[i], lv_color_hex(0x1E293B), 0);
        lv_obj_add_event_cb(ai_qbtns[i], [](lv_event_t * e) {
            const char* p = (const char*)lv_event_get_user_data(e);
            triggerAIPrompt(p);
        }, LV_EVENT_CLICKED, (void*)qPrompts[i]);

        lv_obj_t * qlbl = lv_label_create(ai_qbtns[i]);
        lv_label_set_text(qlbl, qLabels[i]);
        lv_obj_center(qlbl);
    }

    kb = lv_keyboard_create(current_screen);
    lv_obj_set_size(kb, 320, 114);
    lv_obj_align(kb, LV_ALIGN_BOTTOM_MID, 0, 0);
    lv_keyboard_set_textarea(kb, ai_ta_in);
    lv_obj_add_event_cb(kb, ai_kb_event_cb, LV_EVENT_ALL, NULL);
    lv_obj_add_flag(kb, LV_OBJ_FLAG_HIDDEN);
}

/* === APLIKACE 4: WI-FI NASTAVENÍ (S TLAČÍTKEM PRIPOJIT!) === */
void saveAndConnectWifiFromUI() {
    if (dd_ssid == NULL || ta_pass == NULL) return;
    char selected_ssid[64] = "";
    lv_dropdown_get_selected_str(dd_ssid, selected_ssid, sizeof(selected_ssid));
    
    if (strcmp(selected_ssid, "Hledam site...") != 0 && 
        strcmp(selected_ssid, "Prosim cekejte") != 0 && 
        strcmp(selected_ssid, "Zadne site v okoli") != 0 &&
        strlen(selected_ssid) > 0) {
        
        strncpy(current_ssid, selected_ssid, sizeof(current_ssid) - 1);
        current_ssid[sizeof(current_ssid) - 1] = '\0';
        
        strncpy(current_pass, lv_textarea_get_text(ta_pass), sizeof(current_pass) - 1);
        current_pass[sizeof(current_pass) - 1] = '\0';
        
        preferences.putString("ssid", String(current_ssid));
        preferences.putString("pass", String(current_pass));
        wifi_connect_request = true;
    }
    launchApp(APP_LAUNCHER);
}

static void ta_event_cb(lv_event_t * e) {
    lv_event_code_t code = lv_event_get_code(e);
    lv_obj_t * ta = lv_event_get_target(e);
    if (code == LV_EVENT_CLICKED || code == LV_EVENT_FOCUSED) {
        if (kb != NULL) lv_keyboard_set_textarea(kb, ta);
    }
}

static void kb_event_cb(lv_event_t * e) {
    lv_event_code_t code = lv_event_get_code(e);
    if (code == LV_EVENT_READY) { 
        saveAndConnectWifiFromUI();
    }
}

void create_wifi_screen() {
    lv_obj_set_style_bg_color(current_screen, lv_color_hex(0x222222), 0);

    lv_obj_t * btn_back = lv_btn_create(current_screen);
    lv_obj_set_size(btn_back, 58, 32);
    lv_obj_align(btn_back, LV_ALIGN_TOP_LEFT, 5, 5);
    lv_obj_set_style_bg_color(btn_back, lv_color_hex(0xAA0000), 0);
    lv_obj_add_event_cb(btn_back, btn_back_cb, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_back = lv_label_create(btn_back);
    lv_label_set_text(lbl_back, "ZPET");
    lv_obj_center(lbl_back);

    // Zelené tlačítko PRIPOJIT (aby uživatel nemusel hledat malou fajfku na klávesnici)
    lv_obj_t * btn_conn = lv_btn_create(current_screen);
    lv_obj_set_size(btn_conn, 86, 32);
    lv_obj_align(btn_conn, LV_ALIGN_TOP_LEFT, 68, 5);
    lv_obj_set_style_bg_color(btn_conn, lv_color_hex(0x16A34A), 0);
    lv_obj_add_event_cb(btn_conn, [](lv_event_t * e) {
        saveAndConnectWifiFromUI();
    }, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_conn = lv_label_create(btn_conn);
    lv_label_set_text(lbl_conn, "PRIPOJIT");
    lv_obj_center(lbl_conn);

    dd_ssid = lv_dropdown_create(current_screen);
    lv_dropdown_set_options(dd_ssid, "Hledam site...\nProsim cekejte");
    lv_obj_set_width(dd_ssid, 150);
    lv_obj_align(dd_ssid, LV_ALIGN_TOP_LEFT, 5, 42);

    ta_pass = lv_textarea_create(current_screen);
    lv_textarea_set_one_line(ta_pass, true);
    lv_textarea_set_password_mode(ta_pass, false); // Heslo je viditelné při psaní na malém displeji
    lv_obj_set_width(ta_pass, 150);
    lv_obj_align(ta_pass, LV_ALIGN_TOP_RIGHT, -5, 42);
    lv_textarea_set_text(ta_pass, current_pass);
    lv_textarea_set_placeholder_text(ta_pass, "Heslo Wi-Fi...");
    lv_obj_add_event_cb(ta_pass, ta_event_cb, LV_EVENT_ALL, NULL);

    kb = lv_keyboard_create(current_screen);
    lv_keyboard_set_textarea(kb, ta_pass); 
    lv_obj_add_event_cb(kb, kb_event_cb, LV_EVENT_READY, NULL);
}

/* === APLIKACE 3: 3D ENGINE === */
void create_doom_screen() {
    lv_obj_set_style_bg_color(current_screen, lv_color_hex(0x000000), 0);
    
    lv_obj_t * touch_area = lv_obj_create(current_screen);
    lv_obj_remove_style_all(touch_area);
    lv_obj_set_size(touch_area, 320, 240);
    lv_obj_add_flag(touch_area, LV_OBJ_FLAG_CLICKABLE);
    lv_obj_add_event_cb(touch_area, doom_touch_cb, LV_EVENT_ALL, NULL);

    lv_obj_t * btn_back = lv_btn_create(current_screen);
    lv_obj_set_size(btn_back, 60, 30);
    lv_obj_align(btn_back, LV_ALIGN_TOP_MID, 0, 3); 
    lv_obj_set_style_bg_color(btn_back, lv_color_hex(0xAA0000), 0);
    lv_obj_add_event_cb(btn_back, btn_back_cb, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_back = lv_label_create(btn_back);
    lv_label_set_text(lbl_back, "ZPET");
    lv_obj_center(lbl_back);
}

void drawClippedRect3D(int x, int y, int w, int h, uint16_t color) {
    if (h <= 0 || w <= 0) return;
    int y_end = y + h;
    if (y < VIEW_TOP) y = VIEW_TOP;
    if (y_end > screenHeight) y_end = screenHeight;
    if (y_end > y) {
        tft.fillRect(x, y, w, y_end - y, color);
    }
}

void update_hybrid_doom() {
    if (activeApp != APP_DOOM || zBuffer == NULL) return;

    const float moveSpeed = 0.10f;
    const float rotSpeed = 0.08f;
    const float collisionR = 0.25f; 
    bool isMoving = false;

    int activeAction = (doom_action != 0) ? doom_action : (int)web_doom_action;

    if (activeAction == 3) playerAngle -= rotSpeed;
    if (activeAction == 4) playerAngle += rotSpeed;
    if (activeAction == 1 || activeAction == 2) {
        float dir = (activeAction == 1) ? 1.0f : -1.0f;
        float dx = cosf(playerAngle) * moveSpeed * dir;
        float dy = sinf(playerAngle) * moveSpeed * dir;
        float marginX = (dx >= 0.0f) ? collisionR : -collisionR;
        float marginY = (dy >= 0.0f) ? collisionR : -collisionR;

        if (worldMap[(int)playerY][(int)(playerX + dx + marginX)] == 0) playerX += dx;
        if (worldMap[(int)(playerY + dy + marginY)][(int)playerX] == 0) playerY += dy;
        isMoving = true;
    }

    if (isMoving) walkTimer += 0.35f;
    else walkTimer = 0.0f; 
    int zOffset = (int)(sinf(walkTimer) * 6.0f); 

    const float fov = 1.047198f; 
    const float halfFov = fov / 2.0f;
    const int stripWidth = 4; 

    tft.startWrite(); 

    for (int x = 0; x < 320; x += stripWidth) {
        float rayAngle = (playerAngle - halfFov) + ((float)x / 320.0f) * fov;
        float rayDirX = cosf(rayAngle);
        float rayDirY = sinf(rayAngle);

        int mapX = (int)playerX;
        int mapY = (int)playerY;

        float deltaDistX = (fabsf(rayDirX) < 1e-5f) ? 1e30f : fabsf(1.0f / rayDirX);
        float deltaDistY = (fabsf(rayDirY) < 1e-5f) ? 1e30f : fabsf(1.0f / rayDirY);
        float sideDistX, sideDistY;
        int stepX, stepY;

        if (rayDirX < 0) {
            stepX = -1;
            sideDistX = (playerX - mapX) * deltaDistX;
        } else {
            stepX = 1;
            sideDistX = (mapX + 1.0f - playerX) * deltaDistX;
        }
        if (rayDirY < 0) {
            stepY = -1;
            sideDistY = (playerY - mapY) * deltaDistY;
        } else {
            stepY = 1;
            sideDistY = (mapY + 1.0f - playerY) * deltaDistY;
        }

        int hit = 0;
        int side = 0; 
        int hitType = 1;

        while (hit == 0) {
            if (sideDistX < sideDistY) {
                sideDistX += deltaDistX;
                mapX += stepX;
                side = 0;
            } else {
                sideDistY += deltaDistY;
                mapY += stepY;
                side = 1;
            }
            if (mapX < 0 || mapX >= mapW || mapY < 0 || mapY >= mapH) {
                hit = 1;
            } else if (worldMap[mapY][mapX] > 0) {
                hit = 1;
                hitType = worldMap[mapY][mapX];
            }
        }

        float rawDist = (side == 0) ? (sideDistX - deltaDistX) : (sideDistY - deltaDistY);
        if (rawDist < 0.1f) rawDist = 0.1f;

        float correctedDist = rawDist * cosf(rayAngle - playerAngle);
        if (correctedDist < 0.1f) correctedDist = 0.1f;

        zBuffer[x / stripWidth] = correctedDist;

        int lineHeight = (int)(VIEW_HEIGHT / correctedDist);
        int ceiling = VIEW_HORIZON - (lineHeight / 2) + zOffset;
        int floor = VIEW_HORIZON + (lineHeight / 2) + zOffset;

        int r = 0, g = 0, b = 0;
        if (hitType == 1)      { r = 230; g = 35;  b = 35;  } 
        else if (hitType == 2) { r = 40;  g = 110; b = 250; } 
        else if (hitType == 3) { r = 0;   g = 255; b = 120; } 

        float shade = 1.0f - (rawDist / 10.0f);
        if (shade < 0.1f) shade = 0.1f;
        if (side == 1) shade *= 0.72f; 

        uint16_t wallColor = tft.color565((uint8_t)(r * shade), (uint8_t)(g * shade), (uint8_t)(b * shade));

        drawClippedRect3D(x, VIEW_TOP, stripWidth, ceiling - VIEW_TOP, tft.color565(25, 25, 25)); 
        drawClippedRect3D(x, ceiling, stripWidth, floor - ceiling, wallColor);                    
        drawClippedRect3D(x, floor, stripWidth, screenHeight - floor, tft.color565(55, 55, 55));  
    }

    int aimedTargetIdx = -1;
    for (int i = 0; i < 3; i++) {
        if (targets[i].active && (millis() - targets[i].lastTime < KEEPALIVE_MS)) {
            float dx = targets[i].smoothWorldX - playerX;
            float dy = targets[i].smoothWorldY - playerY;
            float distToTarget = sqrtf(dx * dx + dy * dy);

            if (distToTarget > 0.15f) {
                float angleToTarget = atan2f(dy, dx);
                float angleDiff = angleToTarget - playerAngle;
                while (angleDiff < -PI) angleDiff += 2.0f * PI;
                while (angleDiff > PI) angleDiff -= 2.0f * PI;

                if (fabsf(angleDiff) < 0.85f) {
                    int screenX = (int)(160.0f + (angleDiff / halfFov) * 160.0f);
                    float perpDist = distToTarget * cosf(angleDiff);
                    if (perpDist < 0.15f) perpDist = 0.15f;

                    int spriteSize = (int)(VIEW_HEIGHT / perpDist);
                    if (spriteSize > 500) spriteSize = 500;

                    int top = VIEW_HORIZON - (spriteSize / 2) + zOffset;
                    int width = spriteSize / 2;
                    int left = screenX - (width / 2);
                    int right = screenX + (width / 2);

                    if (160 >= left && 160 <= right) {
                        aimedTargetIdx = i;
                    }

                    uint16_t spriteColor = getSpeedColor(abs(targets[i].speed));

                    for (int sx = left; sx < right; sx += stripWidth) {
                        int zIdx = sx / stripWidth;
                        if (sx >= 0 && sx < 320 && zIdx >= 0 && zIdx < 80) {
                            if (perpDist < zBuffer[zIdx]) {
                                int u = ((sx - left) * 100) / (width > 0 ? width : 1);
                                if (u > 30 && u < 70) 
                                    drawClippedRect3D(sx, top, stripWidth, spriteSize / 5, TFT_WHITE);
                                if (u > 20 && u < 80) 
                                    drawClippedRect3D(sx, top + (spriteSize / 4), stripWidth, spriteSize / 2, spriteColor);
                                if ((u > 20 && u < 42) || (u > 58 && u < 80)) 
                                    drawClippedRect3D(sx, top + (spriteSize * 3 / 4), stripWidth, spriteSize / 4, spriteColor);
                            }
                        }
                    }
                }
            }
        }
    }
    aimedTargetGlobal = aimedTargetIdx;

    uint16_t crossColor = (aimedTargetIdx >= 0) ? TFT_GREEN : TFT_WHITE;
    tft.drawFastHLine(155, VIEW_HORIZON, 11, crossColor);
    tft.drawFastVLine(160, VIEW_HORIZON - 5, 11, crossColor);

    tft.drawFastHLine(0, VIEW_TOP - 1, 320, tft.color565(80, 80, 80));

    tft.setTextSize(1);
    if (aimedTargetIdx >= 0) {
        tft.setTextColor(TFT_GREEN, TFT_BLACK);
        tft.setCursor(5, 6);
        tft.printf("LOCK C%d: %dcm   ", aimedTargetIdx + 1, (int)targets[aimedTargetIdx].dist);
        tft.setCursor(5, 18);
        tft.printf("SPD: %d cm/s    ", abs((int)targets[aimedTargetIdx].speed));
    } else {
        tft.setTextColor(tft.color565(150, 150, 150), TFT_BLACK);
        tft.setCursor(5, 6);
        tft.print("3D AR SCANNER   ");
        tft.setCursor(5, 18);
        tft.print("Zamer cil...    ");
    }

    int mapOffsetX = 284;
    int mapOffsetY = 2;
    int blockSize = 4;
    for (int my = 0; my < mapH; my++) {
        for (int mx = 0; mx < mapW; mx++) {
            uint16_t cellColor = TFT_BLACK; 
            if (worldMap[my][mx] == 3) cellColor = TFT_GREEN;
            else if (worldMap[my][mx] > 0) cellColor = tft.color565(100, 100, 100);
            tft.fillRect(mapOffsetX + mx * blockSize, mapOffsetY + my * blockSize, blockSize, blockSize, cellColor);
        }
    }

    for (int i = 0; i < 3; i++) {
        if (targets[i].active && (millis() - targets[i].lastTime < KEEPALIVE_MS)) {
            float clampedX = constrain(targets[i].smoothWorldX, 1.0f, (float)(mapW - 1));
            float clampedY = constrain(targets[i].smoothWorldY, 1.0f, (float)(mapH - 1));
            tft.fillCircle(mapOffsetX + (int)(clampedX * blockSize), mapOffsetY + (int)(clampedY * blockSize), 1, TFT_ORANGE);
        }
    }

    tft.fillCircle(mapOffsetX + (int)(playerX * blockSize), mapOffsetY + (int)(playerY * blockSize), 1, TFT_CYAN);

    tft.endWrite(); 
}

/* === APLIKACE 2: POKROČILÝ 2D RADAR === */
void create_radar_screen() {
    lv_obj_set_style_bg_color(current_screen, lv_color_hex(0x000000), 0);

    lv_obj_t * radar_touch = lv_obj_create(current_screen);
    lv_obj_remove_style_all(radar_touch);
    lv_obj_set_size(radar_touch, 320, 240);
    lv_obj_add_flag(radar_touch, LV_OBJ_FLAG_CLICKABLE);
    lv_obj_add_event_cb(radar_touch, radar_touch_cb, LV_EVENT_PRESSED, NULL);

    lv_obj_t * btn_back = lv_btn_create(current_screen);
    lv_obj_set_size(btn_back, 70, 34);
    lv_obj_align(btn_back, LV_ALIGN_TOP_LEFT, 5, 4);
    lv_obj_set_style_bg_color(btn_back, lv_color_hex(0x000000), 0); 
    lv_obj_set_style_border_color(btn_back, lv_color_hex(0xAA0000), 0); 
    lv_obj_set_style_border_width(btn_back, 2, 0);
    lv_obj_add_event_cb(btn_back, btn_back_cb, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_back = lv_label_create(btn_back);
    lv_label_set_text(lbl_back, "ZPET");
    lv_obj_set_style_text_color(lbl_back, lv_color_hex(0xFF5555), 0);
    lv_obj_center(lbl_back);
    
    lv_obj_t * btn_mode = lv_btn_create(current_screen);
    lv_obj_set_size(btn_mode, 80, 34);
    lv_obj_align(btn_mode, LV_ALIGN_TOP_RIGHT, -5, 4);
    lv_obj_set_style_bg_color(btn_mode, lv_color_hex(0x000000), 0); 
    lv_obj_set_style_border_color(btn_mode, lv_color_hex(0x00AA00), 0); 
    lv_obj_set_style_border_width(btn_mode, 2, 0);
    lv_obj_add_event_cb(btn_mode, btn_mode_cb, LV_EVENT_CLICKED, NULL);
    btn_mode_label = lv_label_create(btn_mode);
    lv_label_set_text(btn_mode_label, radar_pulse_mode ? "PULSE" : "LIVE");
    lv_obj_set_style_text_color(btn_mode_label, lv_color_hex(0x00FF00), 0);
    lv_obj_center(btn_mode_label);
    
    locked_target_idx = -1;
    radar_needs_grid = true;
}

/* === PARSER + GLOBÁLNÍ NEAREST-NEIGHBOR TRACKING === */
void assignReadingToTarget(int idx, const RawReading &r, bool isNewTarget) {
    unsigned long now = millis();
    targets[idx].raw_x = r.x_mm;
    targets[idx].raw_y = r.y_mm;
    targets[idx].x = r.sx;
    targets[idx].y = r.sy;
    targets[idx].dist = r.dist_cm;
    targets[idx].speed = r.speed_cms;
    targets[idx].gate_res_mm = r.gate_mm;
    targets[idx].angle_deg = r.angle_deg;

    float rawWorldX = RADAR_VIRTUAL_X - (r.x_mm / 1000.0f);
    float rawWorldY = RADAR_VIRTUAL_Y + (r.y_mm / 1000.0f);

    if (isNewTarget || !targets[idx].active || targets[idx].smoothX == 0.0f) {
        targets[idx].smoothX = r.sx;
        targets[idx].smoothY = r.sy;
        targets[idx].velX = 0.0f;
        targets[idx].velY = 0.0f;
        targets[idx].smoothWorldX = rawWorldX;
        targets[idx].smoothWorldY = rawWorldY;
        targets[idx].trailCount = 0;
    } else {
        float prevSmoothX = targets[idx].smoothX;
        float prevSmoothY = targets[idx].smoothY;

        targets[idx].smoothX += ((float)r.sx - prevSmoothX) * SMOOTH_POS;
        targets[idx].smoothY += ((float)r.sy - prevSmoothY) * SMOOTH_POS;

        float stepVx = targets[idx].smoothX - prevSmoothX;
        float stepVy = targets[idx].smoothY - prevSmoothY;

        if (abs(r.speed_cms) < 5 && hypotf(stepVx, stepVy) < 0.8f) {
            targets[idx].velX *= 0.25f;
            targets[idx].velY *= 0.25f;
        } else {
            targets[idx].velX = targets[idx].velX * 0.60f + stepVx * 0.40f;
            targets[idx].velY = targets[idx].velY * 0.60f + stepVy * 0.40f;
        }

        targets[idx].smoothWorldX += (rawWorldX - targets[idx].smoothWorldX) * SMOOTH_POS;
        targets[idx].smoothWorldY += (rawWorldY - targets[idx].smoothWorldY) * SMOOTH_POS;
    }

    int curX = (int)roundf(targets[idx].smoothX);
    int curY = (int)roundf(targets[idx].smoothY);
    bool addTrail = false;
    if (targets[idx].trailCount == 0) {
        addTrail = true;
    } else {
        int prevX = targets[idx].trailX[targets[idx].trailCount - 1];
        int prevY = targets[idx].trailY[targets[idx].trailCount - 1];
        float moveDist = hypotf((float)(curX - prevX), (float)(curY - prevY));
        if (moveDist >= 5.0f && (now - targets[idx].lastTrailTime >= 110)) {
            addTrail = true;
        }
    }

    if (addTrail) {
        if (targets[idx].trailCount < TRAIL_LEN) {
            targets[idx].trailX[targets[idx].trailCount] = curX;
            targets[idx].trailY[targets[idx].trailCount] = curY;
            targets[idx].trailCount++;
        } else {
            for (int t = 0; t < TRAIL_LEN - 1; t++) {
                targets[idx].trailX[t] = targets[idx].trailX[t + 1];
                targets[idx].trailY[t] = targets[idx].trailY[t + 1];
            }
            targets[idx].trailX[TRAIL_LEN - 1] = curX;
            targets[idx].trailY[TRAIL_LEN - 1] = curY;
        }
        targets[idx].lastTrailTime = now;
    }

    targets[idx].lastTime = now;
    targets[idx].active = true;
}

void updateRawTargets(byte* data) {
    radar_frame_counter++;
    RawReading raw[3];
    unsigned long now = millis();
    int maxDistCm = current_max_y_mm / 10;

    for (int i = 0; i < 3; i++) {
        int offset = i * 8; 
        int16_t x_raw = data[offset] | (data[offset + 1] << 8);
        int16_t y_raw = data[offset + 2] | (data[offset + 3] << 8);
        int16_t speed_raw = data[offset + 4] | (data[offset + 5] << 8);
        uint16_t gate_raw = data[offset + 6] | (data[offset + 7] << 8);

        bool x_sign = x_raw & 0x8000;
        bool speed_sign = speed_raw & 0x8000;
        x_raw &= 0x7FFF; y_raw &= 0x7FFF; speed_raw &= 0x7FFF;
        if (x_sign) x_raw = -x_raw;
        if (speed_sign) speed_raw = -speed_raw; 

        if (x_raw == 0 && y_raw == 0) continue; 
        
        int dist = (int)(sqrtf((float)x_raw * x_raw + (float)y_raw * y_raw) / 10.0f);
        if (dist < MIN_DIST_CM || dist > maxDistCm) continue; 

        raw[i].valid = true;
        raw[i].x_mm = x_raw;
        raw[i].y_mm = y_raw;
        raw[i].speed_cms = speed_raw;
        raw[i].gate_mm = gate_raw;
        raw[i].dist_cm = dist;
        raw[i].sx = centerX - ((long)x_raw * RADAR_R_MAX / current_max_y_mm);
        raw[i].sy = centerY - ((long)y_raw * RADAR_R_MAX / current_max_y_mm);
        raw[i].angle_deg = atan2f((float)x_raw, (float)y_raw) * 57.29578f;
    }

    bool targetClaimed[3] = {false, false, false};

    for (int pass = 0; pass < 3; pass++) {
        int bestR = -1;
        int bestT = -1;
        float bestDistMm = 1600.0f;

        for (int r = 0; r < 3; r++) {
            if (!raw[r].valid || raw[r].matched) continue;
            for (int t = 0; t < 3; t++) {
                if (targetClaimed[t]) continue;
                if (targets[t].active && (now - targets[t].lastTime < KEEPALIVE_MS)) {
                    float dMm = hypotf((float)(raw[r].x_mm - targets[t].raw_x), (float)(raw[r].y_mm - targets[t].raw_y));
                    if (dMm < bestDistMm) {
                        bestDistMm = dMm;
                        bestR = r;
                        bestT = t;
                    }
                }
            }
        }

        if (bestR >= 0 && bestT >= 0) {
            assignReadingToTarget(bestT, raw[bestR], false);
            raw[bestR].matched = true;
            targetClaimed[bestT] = true;
        } else {
            break;
        }
    }

    for (int r = 0; r < 3; r++) {
        if (!raw[r].valid || raw[r].matched) continue;
        int freeSlot = -1;
        for (int t = 0; t < 3; t++) {
            bool isExpired = (now - targets[t].lastTime >= KEEPALIVE_MS);
            if (!targetClaimed[t] && (!targets[t].active || isExpired)) {
                freeSlot = t;
                break;
            }
        }
        if (freeSlot >= 0) {
            assignReadingToTarget(freeSlot, raw[r], true);
            raw[r].matched = true;
            targetClaimed[freeSlot] = true;
        }
    }
}

void drawRawStaticGrid() {
    int r_step = RADAR_R_MAX / 4; 
    tft.setTextSize(1);
    tft.setTextColor(RADAR_GRID, RADAR_BG); 

    for (int i = 1; i <= 4; i++) {
        int r = r_step * i;
        tft.drawCircle(centerX, centerY, r, RADAR_GRID);
        tft.setCursor(centerX + 4, centerY - r + 2);
        float ringMeters = (current_max_y_mm / 4000.0f) * i;
        if (current_max_y_mm == 2000 || current_max_y_mm == 6000) {
            tft.printf("%.1fm", ringMeters);
        } else {
            tft.printf("%dm", (int)ringMeters);
        }
    }

    tft.drawLine(centerX, centerY, centerX, centerY - RADAR_R_MAX, RADAR_GRID); 

    int x30 = (int)(RADAR_R_MAX * 0.500f);  
    int y30 = (int)(RADAR_R_MAX * 0.866f);  
    tft.drawLine(centerX, centerY, centerX - x30, centerY - y30, RADAR_GRID);
    tft.drawLine(centerX, centerY, centerX + x30, centerY - y30, RADAR_GRID);

    int x60 = (int)(RADAR_R_MAX * 0.866f);  
    int y60 = (int)(RADAR_R_MAX * 0.500f);  
    tft.drawLine(centerX, centerY, centerX - x60, centerY - y60, RADAR_CONE);
    tft.drawLine(centerX, centerY, centerX + x60, centerY - y60, RADAR_CONE);

    tft.setTextColor(RADAR_CONE, RADAR_BG);
    tft.setCursor(4, centerY - y60 - 10);
    tft.print("-60");
    tft.setCursor(screenWidth - 24, centerY - y60 - 10);
    tft.print("+60");
}

void eraseTargetVisuals(int i) {
    for (int t = 0; t < targets[i].lastTrailCount; t++) {
        tft.fillCircle(targets[i].lastTrailX[t], targets[i].lastTrailY[t], 2, RADAR_BG);
    }
    targets[i].lastTrailCount = 0;

    if (targets[i].hadVec) {
        tft.drawLine(targets[i].lastX, targets[i].lastY, targets[i].lastVecX, targets[i].lastVecY, RADAR_BG);
        tft.fillCircle(targets[i].lastVecX, targets[i].lastVecY, 2, RADAR_BG);
        targets[i].hadVec = false;
    }

    if (targets[i].lastGateR > 0) {
        tft.drawCircle(targets[i].lastX, targets[i].lastY, targets[i].lastGateR, RADAR_BG);
        targets[i].lastGateR = 0;
    }

    if (targets[i].hadLockBox) {
        int boxR = targets[i].lastR + 5;
        tft.drawRect(targets[i].lastX - boxR, targets[i].lastY - boxR, boxR * 2 + 1, boxR * 2 + 1, RADAR_BG);
        targets[i].hadLockBox = false;
    }

    if (targets[i].lastR > 0) {
        tft.fillCircle(targets[i].lastX, targets[i].lastY, targets[i].lastR + 1, RADAR_BG);
        targets[i].lastR = 0;
    }
}

void update_hybrid_radar() {
    if (activeApp != APP_RADAR) return;
    int maxDistCm = current_max_y_mm / 10;

    if (radar_pulse_mode && echos != NULL) {
        for (int i = 0; i < MAX_ECHOS; i++) {
            if (echos[i].lastR > 0) {
                tft.fillCircle(echos[i].lastX, echos[i].lastY, echos[i].lastR + 1, RADAR_BG);
                echos[i].lastR = 0;
                radar_needs_grid = true;
            }
        }
        if (lastPulseRadius > 0) {
            tft.drawCircle(centerX, centerY, (int)lastPulseRadius, RADAR_BG);
            radar_needs_grid = true;
        }
        for (int i = 0; i < 3; i++) {
            if (targets[i].active && (millis() - targets[i].lastTime >= KEEPALIVE_MS)) {
                targets[i].active = false;
                targets[i].trailCount = 0;
            }
        }

        lastPulseRadius = pulseRadius;
        pulseRadius += PULSE_SPEED;
        if (pulseRadius > RADAR_R_MAX) { pulseRadius = 0; lastPulseRadius = 0; }

        for (int i = 0; i < 3; i++) {
            if (targets[i].active) {
                float dx = targets[i].x - centerX;
                float dy = targets[i].y - centerY;
                float distPx = sqrtf(dx * dx + dy * dy);

                if (lastPulseRadius <= (distPx + 3.0f) && pulseRadius >= (distPx - 3.0f)) {
                    int targetRadius = map(constrain((int)targets[i].dist, 50, maxDistCm), 50, maxDistCm, 9, 4);
                    uint16_t dotColor = getSpeedColor(abs(targets[i].speed));

                    int slot = -1;
                    for (int e = 0; e < MAX_ECHOS; e++) {
                        if (echos[e].active && hypotf(echos[e].x - targets[i].x, echos[e].y - targets[i].y) < 25.0f) {
                            slot = e; break;
                        }
                    }
                    if (slot == -1) {
                        int minLife = 999;
                        for (int e = 0; e < MAX_ECHOS; e++) {
                            if (!echos[e].active) { slot = e; break; }
                            if (echos[e].life < minLife) { minLife = echos[e].life; slot = e; }
                        }
                    }
                    if (slot >= 0) {
                        echos[slot].active = true;
                        echos[slot].x = targets[i].x;
                        echos[slot].y = max((int)targets[i].y, 48 + targetRadius);
                        echos[slot].r = targetRadius;
                        echos[slot].dist = targets[i].dist;
                        echos[slot].baseColor = dotColor;
                        echos[slot].life = 255;
                    }
                }
            }
        }

        int activeEchoCount = 0;
        for (int e = 0; e < MAX_ECHOS; e++) {
            if (echos[e].active && echos[e].life > 0) activeEchoCount++;
        }

        tft.setTextSize(1);
        tft.setTextColor(SWEEP_COLOR, RADAR_BG);
        tft.setCursor(4, 46);
        tft.printf("ODRAZY: %2d ", activeEchoCount);

        if (radar_needs_grid) {
            drawRawStaticGrid();
            radar_needs_grid = false;
        }
        if (pulseRadius > 0) tft.drawCircle(centerX, centerY, (int)pulseRadius, SWEEP_COLOR);

        for (int e = 0; e < MAX_ECHOS; e++) {
            if (echos[e].active && echos[e].life > 0) {
                uint16_t drawColor = tft.alphaBlend(echos[e].life, echos[e].baseColor, RADAR_BG);
                tft.fillCircle(echos[e].x, echos[e].y, echos[e].r, drawColor);
                echos[e].lastX = echos[e].x;
                echos[e].lastY = echos[e].y;
                echos[e].lastR = echos[e].r;
                echos[e].life -= 4;
                if (echos[e].life <= 0) { echos[e].life = 0; echos[e].active = false; }
            }
        }
        return;
    }

    bool needsGridRedraw = radar_needs_grid;
    radar_needs_grid = false;

    for (int i = 0; i < 3; i++) {
        if (targets[i].lastR > 0 || targets[i].lastTrailCount > 0) {
            eraseTargetVisuals(i);
            needsGridRedraw = true;
        }
        if (targets[i].active && (millis() - targets[i].lastTime >= KEEPALIVE_MS)) {
            targets[i].active = false; 
            targets[i].smoothX = 0.0f; 
            targets[i].smoothWorldY = 0.0f;
            targets[i].trailCount = 0;
            if (locked_target_idx == i) {
                locked_target_idx = -1;
                tft.fillRect(236, 44, 84, 65, RADAR_BG);
            }
            tft.fillRect(0, 44 + (i * 12), 95, 12, RADAR_BG);
            needsGridRedraw = true;
        }
    }

    tft.setTextSize(1);
    for (int i = 0; i < 3; i++) {
        if (!targets[i].active) continue;
        uint16_t dotColor = getSpeedColor(abs(targets[i].speed));
        tft.setTextColor((locked_target_idx == i) ? LOCK_COLOR : dotColor, RADAR_BG);
        tft.setCursor(4, 46 + (i * 12));
        tft.printf("%sC%d:%3dcm %+3.0fd", (locked_target_idx == i) ? ">" : " ", i + 1, (int)targets[i].dist, targets[i].angle_deg);
        needsGridRedraw = true;
    }

    if (locked_target_idx >= 0 && targets[locked_target_idx].active) {
        RadarTarget &lt = targets[locked_target_idx];
        tft.setTextColor(LOCK_COLOR, RADAR_BG);
        tft.setCursor(238, 46);
        tft.printf("LOCK CIL %d  ", locked_target_idx + 1);
        tft.setTextColor(TFT_WHITE, RADAR_BG);
        tft.setCursor(238, 58);
        tft.printf("X:%+5dmm   ", (int)lt.raw_x);
        tft.setCursor(238, 70);
        tft.printf("Y:%5dmm   ", (int)lt.raw_y);
        tft.setCursor(238, 82);
        tft.printf("V:%+4dcm/s  ", (int)lt.speed);
        tft.setCursor(238, 94);
        tft.printf("Res:%3dmm   ", lt.gate_res_mm);
        needsGridRedraw = true;
    } else {
        tft.setTextColor(tft.color565(100, 100, 100), RADAR_BG);
        tft.setCursor(238, 46);
        tft.print("Dotyk=LOCK  ");
    }

    if (needsGridRedraw) drawRawStaticGrid();

    for (int i = 0; i < 3; i++) {
        if (!targets[i].active) continue;

        // === PRVNÍ VÝSKYT (v sekci PULSE módu) ===
                    int targetRadius = map(constrain((int)targets[i].dist, 50, maxDistCm), 50, maxDistCm, 9, 4);
                    uint16_t dotColor = getSpeedColor(abs(targets[i].speed));

                    int slot = -1;
                    for (int e = 0; e < MAX_ECHOS; e++) {
                        if (echos[e].active && hypotf(echos[e].x - targets[i].x, echos[e].y - targets[i].y) < 25.0f) {
                            slot = e; break;
                        }
                    }
                    if (slot == -1) {
                        int minLife = 999;
                        for (int e = 0; e < MAX_ECHOS; e++) {
                            if (!echos[e].active) { slot = e; break; }
                            if (echos[e].life < minLife) { minLife = echos[e].life; slot = e; }
                        }
                    }
                    if (slot >= 0) {
                        echos[slot].active = true;
                        echos[slot].x = targets[i].x;
                        echos[slot].y = max((int)targets[i].y, 48 + targetRadius);
                        echos[slot].r = targetRadius;
                        echos[slot].dist = targets[i].dist;
                        echos[slot].baseColor = dotColor;
                        echos[slot].life = 255;
                    }
                }
            }
        }

        int activeEchoCount = 0;
        for (int e = 0; e < MAX_ECHOS; e++) {
            if (echos[e].active && echos[e].life > 0) activeEchoCount++;
        }

        tft.setTextSize(1);
        tft.setTextColor(SWEEP_COLOR, RADAR_BG);
        tft.setCursor(4, 46);
        tft.printf("ODRAZY: %2d ", activeEchoCount);

        if (radar_needs_grid) {
            drawRawStaticGrid();
            radar_needs_grid = false;
        }
        if (pulseRadius > 0) tft.drawCircle(centerX, centerY, (int)pulseRadius, SWEEP_COLOR);

        for (int e = 0; e < MAX_ECHOS; e++) {
            if (echos[e].active && echos[e].life > 0) {
                uint16_t drawColor = tft.alphaBlend(echos[e].life, echos[e].baseColor, RADAR_BG);
                tft.fillCircle(echos[e].x, echos[e].y, echos[e].r, drawColor);
                echos[e].lastX = echos[e].x;
                echos[e].lastY = echos[e].y;
                echos[e].lastR = echos[e].r;
                echos[e].life -= 4;
                if (echos[e].life <= 0) { echos[e].life = 0; echos[e].active = false; }
            }
        }
        return;
    }

    bool needsGridRedraw = radar_needs_grid;
    radar_needs_grid = false;

    for (int i = 0; i < 3; i++) {
        if (targets[i].lastR > 0 || targets[i].lastTrailCount > 0) {
            eraseTargetVisuals(i);
            needsGridRedraw = true;
        }
        if (targets[i].active && (millis() - targets[i].lastTime >= KEEPALIVE_MS)) {
            targets[i].active = false; 
            targets[i].smoothX = 0.0f; 
            targets[i].smoothWorldY = 0.0f;
            targets[i].trailCount = 0;
            if (locked_target_idx == i) {
                locked_target_idx = -1;
                tft.fillRect(236, 44, 84, 65, RADAR_BG);
            }
            tft.fillRect(0, 44 + (i * 12), 95, 12, RADAR_BG);
            needsGridRedraw = true;
        }
    }

    tft.setTextSize(1);
    for (int i = 0; i < 3; i++) {
        if (!targets[i].active) continue;
        uint16_t dotColor = getSpeedColor(abs(targets[i].speed));
        tft.setTextColor((locked_target_idx == i) ? LOCK_COLOR : dotColor, RADAR_BG);
        tft.setCursor(4, 46 + (i * 12));
        tft.printf("%sC%d:%3dcm %+3.0fd", (locked_target_idx == i) ? ">" : " ", i + 1, (int)targets[i].dist, targets[i].angle_deg);
        needsGridRedraw = true;
    }

    if (locked_target_idx >= 0 && targets[locked_target_idx].active) {
        RadarTarget &lt = targets[locked_target_idx];
        tft.setTextColor(LOCK_COLOR, RADAR_BG);
        tft.setCursor(238, 46);
        tft.printf("LOCK CIL %d  ", locked_target_idx + 1);
        tft.setTextColor(TFT_WHITE, RADAR_BG);
        tft.setCursor(238, 58);
        tft.printf("X:%+5dmm   ", (int)lt.raw_x);
        tft.setCursor(238, 70);
        tft.printf("Y:%5dmm   ", (int)lt.raw_y);
        tft.setCursor(238, 82);
        tft.printf("V:%+4dcm/s  ", (int)lt.speed);
        tft.setCursor(238, 94);
        tft.printf("Res:%3dmm   ", lt.gate_res_mm);
        needsGridRedraw = true;
    } else {
        tft.setTextColor(tft.color565(100, 100, 100), RADAR_BG);
        tft.setCursor(238, 46);
        tft.print("Dotyk=LOCK  ");
    }

    if (needsGridRedraw) drawRawStaticGrid();

    for (int i = 0; i < 3; i++) {
        if (!targets[i].active) continue;

        // === DRUHÝ VÝSKYT (v sekci LIVE módu) ===
        int targetRadius = map(constrain((int)targets[i].dist, 50, maxDistCm), 50, maxDistCm, 9, 4);
        targets[i].smoothR += (targetRadius - targets[i].smoothR) * SMOOTH_SIZE;

        int drawX = (int)roundf(targets[i].smoothX);
        int drawY = (int)roundf(targets[i].smoothY);
        int drawR = (int)roundf(targets[i].smoothR);
        if (drawY < (48 + drawR)) drawY = 48 + drawR;

        uint16_t dotColor = getSpeedColor(abs(targets[i].speed));

        targets[i].lastTrailCount = targets[i].trailCount;
        for (int t = 0; t < targets[i].trailCount; t++) {
            uint8_t alpha = map(t + 1, 1, TRAIL_LEN, 45, 160);
            uint16_t trailCol = tft.alphaBlend(alpha, dotColor, RADAR_BG);
            int ty = max((int)targets[i].trailY[t], 46);
            tft.fillCircle(targets[i].trailX[t], ty, 2, trailCol);
            targets[i].lastTrailX[t] = targets[i].trailX[t];
            targets[i].lastTrailY[t] = ty;
        }

        if (locked_target_idx == i && targets[i].gate_res_mm > 0) {
            int gateR = constrain((int)(targets[i].gate_res_mm * RADAR_R_MAX / current_max_y_mm), drawR + 3, drawR + 14);
            if (drawY - gateR >= 44) {
                tft.drawCircle(drawX, drawY, gateR, tft.color565(0, 110, 110));
                targets[i].lastGateR = gateR;
            }
        }

        tft.fillCircle(drawX, drawY, drawR, dotColor);

        float vMag = hypotf(targets[i].velX, targets[i].velY);
        if (vMag > 0.45f && (abs(targets[i].speed) >= 5 || vMag > 0.9f)) {
            int vecLen = constrain((int)(vMag * 4.5f), 8, 22);
            int vxEnd = drawX + (int)((targets[i].velX / vMag) * vecLen);
            int vyEnd = max(46, drawY + (int)((targets[i].velY / vMag) * vecLen));
            tft.drawLine(drawX, drawY, vxEnd, vyEnd, TFT_WHITE);
            tft.fillCircle(vxEnd, vyEnd, 1, TFT_WHITE);
            targets[i].lastVecX = vxEnd;
            targets[i].lastVecY = vyEnd;
            targets[i].hadVec = true;
        }

        if (locked_target_idx == i) {
            int boxR = drawR + 5;
            tft.drawRect(drawX - boxR, drawY - boxR, boxR * 2 + 1, boxR * 2 + 1, LOCK_COLOR);
            targets[i].hadLockBox = true;
        }

        targets[i].lastX = drawX;
        targets[i].lastY = drawY;
        targets[i].lastR = drawR;
    }
}

/* === APLIKACE 3: MALOVÁNÍ === */
void drawThickBrushLine(int x1, int y1, int x2, int y2, uint16_t col) {
    tft.drawLine(x1, y1, x2, y2, col);
    tft.drawLine(x1 + 1, y1, x2 + 1, y2, col);
    tft.drawLine(x1, y1 + 1, x2, y2 + 1, col);
    tft.drawLine(x1 - 1, y1, x2 - 1, y2, col);
    tft.drawLine(x1, y1 - 1, x2, y2 - 1, col);
    tft.fillCircle(x2, y2, 2, col);
}

void create_paint_screen() {
    lv_obj_set_style_bg_color(current_screen, lv_color_hex(0x000000), 0);
    lv_obj_t * draw_area = lv_obj_create(current_screen);
    lv_obj_remove_style_all(draw_area); 
    lv_obj_set_size(draw_area, 250, 240);
    lv_obj_align(draw_area, LV_ALIGN_RIGHT_MID, 0, 0);
    lv_obj_add_flag(draw_area, LV_OBJ_FLAG_CLICKABLE); 
    lv_obj_add_event_cb(draw_area, paint_draw_cb, LV_EVENT_ALL, NULL);

    lv_obj_t * sidebar = lv_obj_create(current_screen);
    lv_obj_remove_style_all(sidebar);
    lv_obj_set_size(sidebar, 70, 240);
    lv_obj_align(sidebar, LV_ALIGN_LEFT_MID, 0, 0);
    lv_obj_set_style_bg_color(sidebar, lv_color_hex(0x222222), 0);
    lv_obj_set_style_bg_opa(sidebar, LV_OPA_COVER, 0);

    lv_obj_t * btn_back = lv_btn_create(sidebar);
    lv_obj_set_size(btn_back, 60, 35);
    lv_obj_align(btn_back, LV_ALIGN_TOP_MID, 0, 5);
    lv_obj_set_style_bg_color(btn_back, lv_color_hex(0xAA0000), 0);
    lv_obj_add_event_cb(btn_back, btn_back_cb, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_back = lv_label_create(btn_back);
    lv_label_set_text(lbl_back, "ZPET");
    lv_obj_center(lbl_back);

    lv_obj_t * btn_clear = lv_btn_create(sidebar);
    lv_obj_set_size(btn_clear, 60, 35);
    lv_obj_align(btn_clear, LV_ALIGN_TOP_MID, 0, 45);
    lv_obj_set_style_bg_color(btn_clear, lv_color_hex(0x444444), 0);
    lv_obj_add_event_cb(btn_clear, paint_clear_cb, LV_EVENT_CLICKED, NULL);
    lv_obj_t * lbl_clear = lv_label_create(btn_clear);
    lv_label_set_text(lbl_clear, "CLR");
    lv_obj_center(lbl_clear);

    uint16_t colors[] = {TFT_WHITE, TFT_RED, TFT_GREEN, TFT_BLUE};
    int colors_hex[] = {0xFFFFFF, 0xFF0000, 0x00FF00, 0x0000FF};
    for (int i = 0; i < 4; i++) {
        color_btns[i] = lv_btn_create(sidebar);
        lv_obj_set_size(color_btns[i], 44, 26);
        lv_obj_align(color_btns[i], LV_ALIGN_TOP_MID, 0, 90 + (i * 35));
        lv_obj_set_style_bg_color(color_btns[i], lv_color_hex(colors_hex[i]), 0);
        lv_obj_set_style_border_color(color_btns[i], lv_color_hex(0xFFFFFF), 0);
        lv_obj_set_style_border_width(color_btns[i], (paint_color == colors[i]) ? 3 : 1, 0);
        lv_obj_add_event_cb(color_btns[i], paint_color_cb, LV_EVENT_CLICKED, (void*)(size_t)colors[i]);
    }
    paint_needs_restore = true;
}

void update_hybrid_paint() {
    if (activeApp != APP_PAINT || webDrawQ == NULL || strokeHistory == NULL) return;

    if (paint_needs_restore) {
        paint_needs_restore = false;
        uint32_t total = strokeTotalCount;
        uint32_t start = (total > MAX_STROKES) ? (total - MAX_STROKES) : 0;
        tft.startWrite();
        for (uint32_t s = start; s < total; s++) {
            StrokeSegment seg = strokeHistory[s % MAX_STROKES];
            drawThickBrushLine(seg.x1, seg.y1, seg.x2, seg.y2, indexToColor(seg.flags & 0x03));
        }
        tft.endWrite();
        webDrawTail = webDrawHead; 
    }

    while (webDrawTail != webDrawHead) {
        StrokeSegment seg = webDrawQ[webDrawTail];
        webDrawTail = (webDrawTail + 1) % WEB_DRAW_Q_SIZE;
        uint16_t col = indexToColor(seg.flags & 0x03);
        drawThickBrushLine(seg.x1, seg.y1, seg.x2, seg.y2, col);
    }

    if (!is_drawing) return;
    int cur_x = paint_x;
    int cur_y = paint_y;
    if (cur_x == last_drawn_x && cur_y == last_drawn_y) return;

    int x1 = (last_drawn_x != -1) ? last_drawn_x : cur_x;
    int y1 = (last_drawn_y != -1) ? last_drawn_y : cur_y;

    drawThickBrushLine(x1, y1, cur_x, cur_y, paint_color);
    recordStroke(x1, y1, cur_x, cur_y, colorToIndex(paint_color), false);

    last_drawn_x = cur_x; 
    last_drawn_y = cur_y;
}

/* === BEZPEČNÉ ZPRACOVÁNÍ DÁLKOVÝCH PŘÍKAZŮ NA JÁDŘE 1 === */
void process_remote_commands() {
    if (paint_ui_dirty) {
        paint_ui_dirty = false;
        updatePaintColorButtonsUI();
    }
    if (relay_ui_dirty) {
        relay_ui_dirty = false;
        updateSmartHomeUI();
    }
    if (ai_response_dirty) {
        ai_response_dirty = false;
        if (activeApp == APP_AI && ai_ta_out != NULL) {
            lv_textarea_set_text(ai_ta_out, ai_response_buf);
            lv_textarea_set_cursor_pos(ai_ta_out, LV_TEXTAREA_CURSOR_LAST);
        }
    }

    if (web_lock_req_x >= 0 && web_lock_req_y >= 0) {
        int lx = web_lock_req_x;
        int ly = web_lock_req_y;
        web_lock_req_x = -1;
        web_lock_req_y = -1;
        performTargetLockAt(lx, ly);
    }

    if (remote_toast_pending) {
        remote_toast_pending = false;
        if (toast_box != NULL && toast_label != NULL) {
            lv_label_set_text(toast_label, remote_toast_text);
            lv_obj_clear_flag(toast_box, LV_OBJ_FLAG_HIDDEN);
            toast_hide_time = millis() + 4000;
        }
    }

    if (toast_hide_time > 0 && millis() >= toast_hide_time) {
        toast_hide_time = 0;
        if (toast_box != NULL) lv_obj_add_flag(toast_box, LV_OBJ_FLAG_HIDDEN);
        lv_refr_now(NULL);
        if (activeApp == APP_RADAR) radar_needs_grid = true;
        if (activeApp == APP_PAINT) paint_needs_restore = true;
    }

    int cmd = remote_cmd;
    if (cmd == 0) return;
    remote_cmd = 0;

    if (cmd == 1)       launchApp(APP_LAUNCHER);
    else if (cmd == 2)  launchApp(APP_RADAR);
    else if (cmd == 3)  launchApp(APP_PAINT);
    else if (cmd == 4)  launchApp(APP_DOOM);
    else if (cmd == 5)  btn_mode_cb(NULL);
    else if (cmd == 6)  clearPaintCanvas();
    else if (cmd == 7)  setRadarHardwareTrackingMode(false); 
    else if (cmd == 8)  setRadarHardwareTrackingMode(true);  
    else if (cmd == 9)  { playerX = 4.5f; playerY = 6.5f; playerAngle = -1.570796f; }
    else if (cmd == 10) {
        if (activeApp == APP_RADAR) {
            tft.fillRect(0, 42, screenWidth, screenHeight - 42, RADAR_BG);
            radar_needs_grid = true;
        }
    }
    else if (cmd == 11) launchApp(APP_HOME);
    else if (cmd == 12) launchApp(APP_AI);
}

/* === OPRAVENÁ HORNÍ LIŠTA S PŘÍMÝM VÝPISEM LOKÁLNÍ IP ADRESY === */
void update_status_bar() {
    static unsigned long last_ip_check = 0;
    unsigned long now = millis();

    // Každých 500 ms ověříme skutečný stav WiFi.localIP(), aby byla IP vždy vidět
    if (status_bar_dirty || (now - last_ip_check >= 500)) {
        last_ip_check = now;
        status_bar_dirty = false;

        if (WiFi.status() == WL_CONNECTED) {
            IPAddress lip = WiFi.localIP();
            if (wg_connected) {
                snprintf(wifi_ip_str, sizeof(wifi_ip_str), "IP: %d.%d.%d.%d | WG", lip[0], lip[1], lip[2], lip[3]);
                lv_obj_set_style_text_color(wifi_icon, lv_color_hex(0x00FFAA), 0);
            } else {
                snprintf(wifi_ip_str, sizeof(wifi_ip_str), "IP: %d.%d.%d.%d", lip[0], lip[1], lip[2], lip[3]);
                lv_obj_set_style_text_color(wifi_icon, lv_color_hex(0x00FF00), 0);
            }
            lv_label_set_text(wifi_icon, wifi_ip_str);
        } else {
            if (strlen(current_ssid) > 0 && activeApp != APP_WIFI) {
                lv_label_set_text(wifi_icon, "Wi-Fi: Pripojuji...");
                lv_obj_set_style_text_color(wifi_icon, lv_color_hex(0xFFAA00), 0);
            } else {
                lv_label_set_text(wifi_icon, "Wi-Fi: OFF");
                lv_obj_set_style_text_color(wifi_icon, lv_color_hex(0xFF5555), 0);
            }
        }
        // Nutné přerovnání po změně délky textu, jinak IP adresa uteče mimo displej!
        lv_obj_align(wifi_icon, LV_ALIGN_TOP_RIGHT, -6, 8);
    }
}

void setup() {
    Serial.begin(115200);
    Serial2.setRxBufferSize(1024); 
    Serial2.begin(RADAR_BAUD_RATE, SERIAL_8N1, RADAR_RX, RADAR_TX);
    
    byte exitConfig[] = {0xFD, 0xFC, 0xFB, 0xFA, 0x02, 0x00, 0xFE, 0x00, 0x04, 0x03, 0x02, 0x01};
    Serial2.write(exitConfig, sizeof(exitConfig));

    strokeHistory = (StrokeSegment*)malloc(MAX_STROKES * sizeof(StrokeSegment));
    webDrawQ      = (StrokeSegment*)malloc(WEB_DRAW_Q_SIZE * sizeof(StrokeSegment));

    // Inicializace síťového adaptéru před startem FreeRTOS tasku (nutné pro Core 3.3.11)
    WiFi.mode(WIFI_STA);

    tft.init();
    tft.setRotation(1);
    tft.setSwapBytes(true); 
    tft.fillScreen(TFT_BLACK);
    
    uint16_t calData[5] = { 403, 3393, 246, 3459, 7 };
    tft.setTouch(calData);

    lv_init();
    lv_disp_draw_buf_init(&draw_buf, buf, NULL, screenWidth * screenHeight / 12); 

    static lv_disp_drv_t disp_drv;
    lv_disp_drv_init(&disp_drv);
    disp_drv.hor_res = screenWidth;
    disp_drv.ver_res = screenHeight;
    disp_drv.flush_cb = my_disp_flush;
    disp_drv.draw_buf = &draw_buf;
    lv_disp_drv_register(&disp_drv);

    static lv_indev_drv_t indev_drv;
    lv_indev_drv_init(&indev_drv);
    indev_drv.type = LV_INDEV_TYPE_POINTER;
    indev_drv.read_cb = my_touchpad_read;
    lv_indev_drv_register(&indev_drv);

    preferences.begin("wifi_cfg", false);
    String saved_ssid = preferences.getString("ssid", "");
    String saved_pass = preferences.getString("pass", "");
    if (saved_ssid.length() > 0) {
        strncpy(current_ssid, saved_ssid.c_str(), sizeof(current_ssid) - 1);
        strncpy(current_pass, saved_pass.c_str(), sizeof(current_pass) - 1);
        wifi_connect_request = true; 
    }

    wifi_icon = lv_label_create(lv_layer_top());
    lv_label_set_text(wifi_icon, "Wi-Fi: OFF");
    lv_obj_set_style_text_color(wifi_icon, lv_color_hex(0xFF5555), 0);
    lv_obj_align(wifi_icon, LV_ALIGN_TOP_RIGHT, -6, 8);

    toast_box = lv_obj_create(lv_layer_top());
    lv_obj_set_size(toast_box, 280, 34);
    lv_obj_align(toast_box, LV_ALIGN_BOTTOM_MID, 0, -6);
    lv_obj_set_style_bg_color(toast_box, lv_color_hex(0x0d1b2a), 0);
    lv_obj_set_style_border_color(toast_box, lv_color_hex(0x00ff88), 0);
    lv_obj_set_style_border_width(toast_box, 2, 0);
    lv_obj_clear_flag(toast_box, LV_OBJ_FLAG_SCROLLABLE);
    toast_label = lv_label_create(toast_box);
    lv_obj_set_style_text_color(toast_label, lv_color_hex(0xFFFFFF), 0);
    lv_obj_center(toast_label);
    lv_obj_add_flag(toast_box, LV_OBJ_FLAG_HIDDEN);

    xTaskCreatePinnedToCore(networkTask, "WiFi_Task", 8192, NULL, 1, NULL, 0);

    launchApp(APP_LAUNCHER);
}

void loop() {
    static uint32_t last_lv_tick = millis();
    uint32_t now = millis();
    lv_tick_inc(now - last_lv_tick);
    last_lv_tick = now;

    if (activeApp == APP_RADAR || activeApp == APP_DOOM) {
        if (now - last_fps_calc >= 1000) {
            radar_fps = radar_frame_counter;
            radar_frame_counter = 0;
            last_fps_calc = now;
        }
        if (now - lastDataTime > 500 && parserState != HEAD1) parserState = HEAD1; 
        while (Serial2.available()) {
            byte b = Serial2.read();
            lastDataTime = millis();
            switch (parserState) {
                case HEAD1: parserState = (b == 0xAA) ? HEAD2 : HEAD1; break;
                case HEAD2: parserState = (b == 0xFF) ? HEAD3 : (b == 0xAA ? HEAD2 : HEAD1); break;
                case HEAD3: parserState = (b == 0x03) ? HEAD4 : (b == 0xAA ? HEAD2 : HEAD1); break;
                case HEAD4: parserState = (b == 0x00) ? DATA  : (b == 0xAA ? HEAD2 : HEAD1); dataIdx = 0; break;
                case DATA:
                    frameData[dataIdx++] = b;
                    if (dataIdx == 24) parserState = TAIL1;
                    break;
                case TAIL1: parserState = (b == 0x55) ? TAIL2 : (b == 0xAA ? HEAD2 : HEAD1); break;
                case TAIL2:
                    if (b == 0xCC) updateRawTargets(frameData); 
                    parserState = HEAD1; 
                    break;
            }
        }
    }

    // Automatické uložení vybrané Wi-Fi sítě a hesla i při odchodu tlačítkem ZPET
    if (activeApp == APP_WIFI) {
        if (wifi_scan_ready) {
            wifi_scan_ready = false;
            if (dd_ssid != NULL) {
                lv_dropdown_set_options(dd_ssid, scan_options_buf);
            }
        }
        static unsigned long last_wifi_form_sync = 0;
        if (now - last_wifi_form_sync >= 250 && dd_ssid != NULL && ta_pass != NULL) {
            last_wifi_form_sync = now;
            char sel_ssid[64] = "";
            lv_dropdown_get_selected_str(dd_ssid, sel_ssid, sizeof(sel_ssid));
            if (strlen(sel_ssid) > 0 &&
                strcmp(sel_ssid, "Hledam site...") != 0 &&
                strcmp(sel_ssid, "Prosim cekejte") != 0 &&
                strcmp(sel_ssid, "Zadne site v okoli") != 0) {
                const char* typed_pass = lv_textarea_get_text(ta_pass);
                if (strcmp(current_ssid, sel_ssid) != 0 || strcmp(current_pass, typed_pass) != 0) {
                    strncpy(current_ssid, sel_ssid, sizeof(current_ssid) - 1);
                    current_ssid[sizeof(current_ssid) - 1] = '\0';
                    strncpy(current_pass, typed_pass, sizeof(current_pass) - 1);
                    current_pass[sizeof(current_pass) - 1] = '\0';
                    preferences.putString("ssid", String(current_ssid));
                    preferences.putString("pass", String(current_pass));
                }
            }
        }
    }

    process_remote_commands();
    lv_timer_handler(); 
    update_status_bar(); 
  
    static unsigned long lastUIUpdate = 0;
    if (millis() - lastUIUpdate >= 30) {
        lastUIUpdate = millis();
        if (activeApp == APP_RADAR)     update_hybrid_radar(); 
        else if (activeApp == APP_DOOM) update_hybrid_doom(); 
    }
  
    if (activeApp == APP_PAINT) {
        update_hybrid_paint(); 
    }
    delay(2);
}
