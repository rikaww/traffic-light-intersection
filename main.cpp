/*
 * 多岔路口(五岔路口)交通信号灯配时设计 —— C++ 版本
 * ======================================================
 * 问题描述:
 *   一个五岔路口有 A、B、C、D、E 五条道路。
 *   其中 C 为"只出"单行道(车辆只能驶出路口到达C,不能从C驶入路口)。
 *   E 为"只进"单行道(车辆只能从E驶入路口,不能驶出到E)。
 *   其余 A、B、D 为双向道路(既可驶入也可驶出)。
 *
 * 建模思路:
 *   1. 路口共有 5 条腿,按图中方位顺时针排列为: C, D, E, A, B
 *      (顺时针顺序决定了各条"路线"在路口内部是否会发生几何交叉)。
 *   2. 允许的驶入方向(entry) = {A, B, D, E}   (C不能驶入)
 *      允许的驶出方向(exit)  = {A, B, D, C}   (E不能驶出)
 *      一条"路线"是一个 (entry, exit) 二元组,且 entry != exit(不含掉头)。
 *      这样共有 4x4 - 3 = 13 条路线,与题目"共有13条可通行路线"完全吻合。
 *   3. 判断两条路线是否冲突:
 *      把 5 条腿看成圆周上的 5 个点,每条路线是圆周上连接 entry 和 exit
 *      两点的一条"弦"。两条路线在路口内部会发生交叉冲突,当且仅当这两条
 *      弦在圆周上是"交叉"的(即一条弦的两个端点被另一条弦的两个端点分隔
 *      在两侧)。若两条路线共享同一个驶入口(同一起点发散)或同一个驶出口
 *      (汇合到同一终点),或者一条路线的终点正好是另一条路线的起点(首尾
 *      相接、不交叉),都不算冲突——这与实际道路几何完全一致。
 *      用这个规则可以验证题目给出的两个例子:
 *        - E→B 与 A→D  会交叉  → 确实不能同时放行 ✔
 *        - A→B 与 E→C  不交叉  → 确实可以同时放行 ✔
 *   4. 有了"冲突关系"就得到一张 13 个节点的冲突图(Conflict Graph)。
 *      给路口设计信号灯配时,本质上就是给这张图做"图着色":
 *        - 每种颜色 = 一个信号灯相位(phase)
 *        - 同一颜色(同一相位)内的路线两两互不冲突,可以同时放绿灯
 *        - 不同颜色(不同相位)的路线不能同时放绿灯
 *      颜色数最少 → 信号相位数最少 → 路口通行效率最高(周期最短)。
 *      本程序用回溯法求出该冲突图的"色数"(最少相位数)及一种最优配色方案。
 *
 * 编译运行:
 *   g++ -std=c++17 -O2 -o traffic_light_control traffic_light_control.cpp
 *   ./traffic_light_control
 */

#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <set>
#include <utility>
#include <algorithm>
#include <thread>
#include <chrono>
#include <functional>

using namespace std;

// ---------- 1. 基础数据 ----------

// 五条腿按图中方位顺时针排列
static const vector<char> LEGS_CLOCKWISE = {'C', 'D', 'E', 'A', 'B'};
static const int N = static_cast<int>(LEGS_CLOCKWISE.size());

static map<char, int> buildPosMap() {
    map<char, int> pos;
    for (int i = 0; i < N; ++i) pos[LEGS_CLOCKWISE[i]] = i;
    return pos;
}
static const map<char, int> POS = buildPosMap();

static const vector<char> ENTRIES = {'A', 'B', 'D', 'E'}; // 可驶入的方向(C 不能驶入)
static const vector<char> EXITS   = {'A', 'B', 'D', 'C'}; // 可驶出的方向(E 不能驶出)

using Move = pair<char, char>; // (entry, exit)

static vector<Move> buildMovements() {
    vector<Move> moves;
    for (char e : ENTRIES)
        for (char x : EXITS)
            if (e != x) moves.emplace_back(e, x);
    return moves;
}
static const vector<Move> MOVEMENTS = buildMovements();

// ---------- 2. 判断两条路线是否几何交叉(冲突) ----------

// 沿顺时针方向,从 a 走到 b(不含端点)途中是否经过 x
static bool strictlyBetween(int x, int a, int b, int n = N) {
    int i = (a + 1) % n;
    while (i != b) {
        if (i == x) return true;
        i = (i + 1) % n;
    }
    return false;
}

// 判断路线 m1=(e1,x1) 与 m2=(e2,x2) 是否会在路口内交叉冲突
static bool conflicts(const Move& m1, const Move& m2) {
    if (m1 == m2) return false;
    int a = POS.at(m1.first), b = POS.at(m1.second);
    int c = POS.at(m2.first), d = POS.at(m2.second);
    return strictlyBetween(c, a, b) != strictlyBetween(d, a, b);
}

// ---------- 3. 构建冲突图 ----------

static vector<pair<Move, Move>> buildConflictEdges() {
    vector<pair<Move, Move>> edges;
    for (size_t i = 0; i < MOVEMENTS.size(); ++i)
        for (size_t j = i + 1; j < MOVEMENTS.size(); ++j)
            if (conflicts(MOVEMENTS[i], MOVEMENTS[j]))
                edges.emplace_back(MOVEMENTS[i], MOVEMENTS[j]);
    return edges;
}
static const vector<pair<Move, Move>> CONFLICT_EDGES = buildConflictEdges();

// ---------- 4. 图着色(求最少信号相位数) ----------

struct ColoringResult {
    int numColors;
    map<Move, int> coloring;
};

static ColoringResult colorGraph(const vector<Move>& nodes,
                                  const vector<pair<Move, Move>>& edges) {
    map<Move, set<Move>> adj;
    for (const auto& v : nodes) adj[v] = {};
    for (const auto& e : edges) {
        adj[e.first].insert(e.second);
        adj[e.second].insert(e.first);
    }

    // 按度数从大到小排序,回溯剪枝效率更高
    vector<Move> order = nodes;
    sort(order.begin(), order.end(), [&](const Move& a, const Move& b) {
        return adj[a].size() > adj[b].size();
    });

    for (int k = 1;; ++k) {
        map<Move, int> coloring;

        // lambda 递归需要 std::function 才能自引用
        std::function<bool(size_t)> backtrack = [&](size_t idx) -> bool {
            if (idx == order.size()) return true;
            const Move& v = order[idx];
            set<int> used;
            for (const auto& u : adj[v]) {
                auto it = coloring.find(u);
                if (it != coloring.end()) used.insert(it->second);
            }
            for (int c = 0; c < k; ++c) {
                if (used.count(c)) continue;
                coloring[v] = c;
                if (backtrack(idx + 1)) return true;
                coloring.erase(v);
            }
            return false;
        };

        if (backtrack(0)) return {k, coloring};
    }
}

// ---------- 5. 生成信号灯相位方案 ----------

static pair<int, map<int, vector<Move>>> buildPhasePlan() {
    ColoringResult result = colorGraph(MOVEMENTS, CONFLICT_EDGES);
    map<int, vector<Move>> phases;
    for (int i = 0; i < result.numColors; ++i) phases[i] = {};
    for (const auto& kv : result.coloring) phases[kv.second].push_back(kv.first);
    return {result.numColors, phases};
}

// ---------- 6. 打印结果 + 简单信号灯运行演示 ----------

static string fmtMove(const Move& m) {
    return string(1, m.first) + "→" + string(1, m.second);
}

static pair<int, map<int, vector<Move>>> printReport() {
    cout << string(60, '=') << "\n";
    cout << "五岔路口 13 条路线\n";
    cout << string(60, '=') << "\n";
    for (const auto& m : MOVEMENTS) cout << "  " << fmtMove(m) << "\n";

    cout << "\n" << string(60, '=') << "\n";
    cout << "冲突关系(共 " << CONFLICT_EDGES.size() << " 对冲突路线)\n";
    cout << string(60, '=') << "\n";
    for (const auto& e : CONFLICT_EDGES)
        cout << "  " << fmtMove(e.first) << "  <->  " << fmtMove(e.second) << "\n";

    auto plan = buildPhasePlan();
    int numPhases = plan.first;
    auto& phases = plan.second;

    cout << "\n" << string(60, '=') << "\n";
    cout << "信号灯配时方案:共需要 " << numPhases << " 个相位(phase)\n";
    cout << string(60, '=') << "\n";
    for (int i = 0; i < numPhases; ++i) {
        cout << "  第 " << (i + 1) << " 相位(绿灯同时放行): ";
        for (size_t j = 0; j < phases[i].size(); ++j) {
            cout << fmtMove(phases[i][j]);
            if (j + 1 < phases[i].size()) cout << ", ";
        }
        cout << "\n";
    }

    cout << "\n" << string(60, '=') << "\n";
    cout << "自检(对照题目给出的例子)\n";
    cout << string(60, '=') << "\n";
    cout << "  E→B 与 A→D 是否冲突(应为 True) : "
         << (conflicts({'E', 'B'}, {'A', 'D'}) ? "true" : "false") << "\n";
    cout << "  A→B 与 E→C 是否冲突(应为 False): "
         << (conflicts({'A', 'B'}, {'E', 'C'}) ? "true" : "false") << "\n";

    return plan;
}

// 简单运行效果演示:按相位顺序循环放行,打印每一秒各路线的信号灯状态。
// 用于作业汇报时展示"代码运行效果"。
static void simulate(int cycles = 1, int secondsPerPhase = 5) {
    auto plan = buildPhasePlan();
    int numPhases = plan.first;
    auto& phases = plan.second;

    cout << "\n" << string(60, '=') << "\n";
    cout << "信号灯运行模拟(演示用)\n";
    cout << string(60, '=') << "\n";

    for (int cycle = 1; cycle <= cycles; ++cycle) {
        for (int p = 0; p < numPhases; ++p) {
            set<Move> green(phases[p].begin(), phases[p].end());
            cout << "\n[周期 " << cycle << " | 第 " << (p + 1) << " 相位] 绿灯放行 "
                 << secondsPerPhase << " 秒:\n";
            for (const auto& m : MOVEMENTS) {
                bool isGreen = green.count(m) > 0;
                cout << "    " << fmtMove(m);
                for (int pad = 0; pad < 6 - (int)fmtMove(m).size(); ++pad) cout << ' ';
                cout << " : " << (isGreen ? "绿灯 GO " : "红灯 STOP") << "\n";
            }
        }
    }
}

int main() {
    printReport();
    simulate(1, 5);
    return 0;
}
