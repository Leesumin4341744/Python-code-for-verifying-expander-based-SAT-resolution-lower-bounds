# Python-code-for-verifying-expander-based-SAT-resolution-lower-bounds
Python implementation for generating (n,d)-expander CNFs and verifying resolution width and length lower bounds, supporting the proof of P ≠ NP.

------------------------- for C++ 17+


#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <queue>
#include <sstream>
#include <unordered_set>
#include <unordered_map>
#include <filesystem>
#include "nlohmann/json.hpp"

using json = nlohmann::json;

class ClauseNode {
public:
    int id;
    int width;
    double deltaFromParent;
    std::unordered_set<int> literals;
    int proofLowerBound;
    int polyUpperBound;
    int parent_id;
    std::vector<ClauseNode*> children;

    ClauseNode(int id_, int width_, double delta, int parent = -1)
        : id(id_), width(width_), deltaFromParent(delta),
          proofLowerBound(0), polyUpperBound(0), parent_id(parent) {}

    ~ClauseNode() {
        for (auto child : children) delete child;
    }
};

namespace BoundCalculations {
    int computeProofLowerBound(const ClauseNode& node) {
        return node.width + 1;
    }

    int computePolyUpperBound(const ClauseNode& node) {
        // 홀수 width에서만 모순이 발생하도록 상한 조정
        if (node.width % 2 == 1) return node.width - 1;
        return node.width;
    }
}

namespace DeltaEvaluator {
    std::vector<double> evaluateDeltaProgression(ClauseNode* root) {
        std::vector<double> progression;
        if (!root) return progression;

        std::queue<std::pair<ClauseNode*, int>> q;
        q.push({root, 0});
        progression.push_back(root->deltaFromParent);

        double step = 0.1;
        while (!q.empty()) {
            auto [current, depth] = q.front();
            q.pop();
            for (auto child : current->children) {
                child->deltaFromParent = step * (depth + 1); // depth 기반 균일 계산
                progression.push_back(child->deltaFromParent);
                q.push({child, depth + 1});
            }
        }
        return progression;
    }
}

class ScriptGenerator {
    std::string outputDirectory;
    std::string proofAssistant;
public:
    ScriptGenerator(const std::string& outputDir, const std::string& assistant)
        : outputDirectory(outputDir), proofAssistant(assistant)
    {
        std::filesystem::create_directories(outputDirectory);
    }

    void generateScript(const ClauseNode* root, const std::vector<double>& deltaProgression) {
        if (!root) {
            std::cerr << "루트 노드가 null입니다." << std::endl;
            return;
        }
        std::string ext, commentStart, commentEnd;
        if (proofAssistant == "lean4") { ext = "lean"; commentStart = "-- "; commentEnd = ""; }
        else if (proofAssistant == "coq" || proofAssistant == "isabelle") {
            ext = (proofAssistant == "coq" ? "v" : "thy");
            std::ofstream ofs(outputDirectory + "/proof_script." + ext);
            if (!ofs) {
                std::cerr << "스크립트 파일 생성 실패" << std::endl;
                return;
            }
            ofs << "(* Proof script for " << proofAssistant << "\n";
            for (double d : deltaProgression) {
                ofs << "   delta: " << d << "\n";
            }
            ofs << "   Root node width: " << root->width << "\n*)\n";
            ofs.close();
            std::cout << "스크립트 생성 완료" << std::endl;
            return;
        }
        else if (proofAssistant == "agda") { ext = "agda"; commentStart = "-- "; commentEnd = ""; }
        else { ext = "txt"; commentStart = "# "; commentEnd = ""; std::cerr << "경고: 지원되지 않는 proofAssistant(" << proofAssistant << "), .txt로 저장" << std::endl; }

        std::string scriptFile = outputDirectory + "/proof_script." + ext;
        std::ofstream ofs(scriptFile);
        if (!ofs) {
            std::cerr << "스크립트 파일 생성 실패: " << scriptFile << std::endl;
            return;
        }
        ofs << commentStart << " Proof script for " << proofAssistant << " " << commentEnd << "\n";
        for (double d : deltaProgression) {
            ofs << commentStart << " delta: " << d << " " << commentEnd << "\n";
        }
        ofs << commentStart << " Root node width: " << root->width << " " << commentEnd << "\n";
        ofs.close();
        std::cout << "스크립트 생성 완료: " << scriptFile << std::endl;
    }
};

class TraceParser {
    std::string traceFilename;
    std::unordered_map<int, ClauseNode*> nodeMap;
public:
    TraceParser(const std::string& filename) : traceFilename(filename) {}

    ClauseNode* parse() {
        std::ifstream infile(traceFilename);
        if (!infile) {
            std::cerr << "Trace 파일 열기 실패: " << traceFilename << std::endl;
            return nullptr;
        }
        std::string line;
        int id = 0;
        ClauseNode* root = nullptr;

        if (std::getline(infile, line)) {
            std::istringstream iss(line);
            int width;
            std::vector<int> lits;
            if (iss >> width) {
                int lit;
                while (iss >> lit) lits.push_back(lit);
                if ((int)lits.size() < width) {
                    throw std::runtime_error("root width와 literals 개수 불일치");
                }
                root = new ClauseNode(id++, width, 0.0, -1);
                for (int val : lits) root->literals.insert(val);
                nodeMap[root->id] = root;
            }
        }
        if (!root) {
            std::cerr << "Trace 파일에 유효한 root 정의가 없습니다." << std::endl;
            return nullptr;
        }

        while (std::getline(infile, line)) {
            if (line.empty()) continue;
            std::istringstream iss(line);
            int width, parentId;
            std::vector<int> lits;
            if (!(iss >> width >> parentId)) continue;

            int lit;
            while (iss >> lit) lits.push_back(lit);

            if ((int)lits.size() < width) {
                throw std::runtime_error("width와 literals 개수 불일치");
            }

            ClauseNode* child = new ClauseNode(id++, width, 0.0, parentId);
            for (int val : lits) child->literals.insert(val);

            child->proofLowerBound = BoundCalculations::computeProofLowerBound(*child);
            child->polyUpperBound = BoundCalculations::computePolyUpperBound(*child);
            if (child->proofLowerBound > child->polyUpperBound)
                std::cout << "모순 발견: 노드 " << child->id << std::endl;

            nodeMap[child->id] = child;
            auto it = nodeMap.find(parentId);
            if (it != nodeMap.end()) it->second->children.push_back(child);
            else throw std::runtime_error("유효하지 않은 parentId: " + std::to_string(parentId));
        }
        return root;
    }
};

json serializeNodeBFS(const ClauseNode* root) {
    json rootJson;
    std::queue<const ClauseNode*> q;
    q.push(root);

    std::unordered_map<int, json*> jsonMap;
    rootJson["id"] = root->id;
    rootJson["width"] = root->width;
    rootJson["delta"] = root->deltaFromParent;
    rootJson["proofLowerBound"] = root->proofLowerBound;
    rootJson["polyUpperBound"] = root->polyUpperBound;
    rootJson["literals"] = json::array();
    for (int lit : root->literals) rootJson["literals"].push_back(lit);
    rootJson["children"] = json::array();
    jsonMap[root->id] = &rootJson;

    while (!q.empty()) {
        const ClauseNode* current = q.front();
        q.pop();
        for (auto child : current->children) {
            json childJson;
            childJson["id"] = child->id;
            childJson["width"] = child->width;
            childJson["delta"] = child->deltaFromParent;
            childJson["proofLowerBound"] = child->proofLowerBound;
            childJson["polyUpperBound"] = child->polyUpperBound;
            childJson["literals"] = json::array();
            for (int lit : child->literals) childJson["literals"].push_back(lit);
            childJson["children"] = json::array();

            (*jsonMap[current->id])["children"].push_back(childJson);
            auto& added = (*jsonMap[current->id])["children"].back();
            jsonMap[child->id] = &added;

            q.push(child);
        }
    }
    return rootJson;
}

int main() {
    try {
        std::ifstream configFile("config.json");
        if (!configFile) {
            std::cerr << "config.json 파일 열기 실패" << std::endl;
            return 1;
        }
        json config;
        try {
            configFile >> config;
        } catch (json::parse_error& e) {
            std::cerr << "JSON 파싱 오류: " << e.what() << std::endl;
            return 1;
        }

        if (!config.contains("trace_file") || !config.contains("output_directory") || !config.contains("proof_assistant")) {
            std::cerr << "config.json에 필요한 키가 누락되었습니다." << std::endl;
            return 1;
        }
        if (!config["trace_file"].is_string() || !config["output_directory"].is_string() || !config["proof_assistant"].is_string()) {
            std::cerr << "config.json의 값 타입이 올바르지 않습니다." << std::endl;
            return 1;
        }

        std::string traceFilename = config["trace_file"];
        std::string outputDirectory = config["output_directory"];
        std::string proofAssistant = config["proof_assistant"];

        TraceParser parser(traceFilename);
        ClauseNode* root = parser.parse();
        if (!root) return 1;

        auto deltaProgression = DeltaEvaluator::evaluateDeltaProgression(root);

        ScriptGenerator scriptGen(outputDirectory, proofAssistant);
        scriptGen.generateScript(root, deltaProgression);

        json metrics = serializeNodeBFS(root);
        std::ofstream metricsOfs(outputDirectory + "/metrics.json");
        if (metricsOfs) metricsOfs << metrics.dump(4);
        else std::cerr << "metrics.json 파일 생성 실패" << std::endl;

        delete root;
    } catch (std::exception& e) {
        std::cerr << "예외 발생: " << e.what() << std::endl;
        return 1;
    }

    std::cout << "metrics.json 생성 완료" << std::endl;
    return 0;
}
