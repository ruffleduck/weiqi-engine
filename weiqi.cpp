#define SIZE 9

#include <array>
#include <cmath>
#include <functional>
#include <iostream>
#include <memory>
#include <stack>
#include <unordered_set>
#include <vector>

using std::array;
using std::log, std::sqrt, std::numeric_limits;
using std::hash;
using std::cin, std::cout, std::endl;
using std::make_unique, std::unique_ptr;
using std::size_t;
using std::stack;
using std::unordered_set;
using std::vector;

struct Pt {
    int row, col;

    bool operator==(const Pt& other) const {
        return row == other.row && col == other.col;
    }
};

class Board { 
    struct PtHash {
        size_t operator()(const Pt& pt) const {
            return hash<int>()(pt.row)^(hash<int>()(pt.col)<<1); 
        }
    };

    enum class Color {
        Black,
        White,
        Empty
    };

    array<array<Color, SIZE>, SIZE> grid;
    Color turnColor = Color::Black;

    array<Pt, 4> adjacent(Pt pt) {
        return {
            Pt{pt.row + 1, pt.col},
            Pt{pt.row - 1, pt.col},
            Pt{pt.row, pt.col + 1},
            Pt{pt.row, pt.col - 1}
        };
    }

    Color getColor(Pt pt) {
        return grid[pt.row][pt.col];
    }

    bool outOfBounds(Pt pt) {
        return
            pt.row < 0 || pt.row >= SIZE ||
            pt.col < 0 || pt.col >= SIZE;
    }

    bool attemptCapture(Pt pt) {
        if (getColor(pt) == Color::Empty || outOfBounds(pt))
            return false;

        unordered_set<Pt, PtHash> visited;
        stack<Pt> toVisit;
        visited.insert(pt);
        toVisit.push(pt);

        bool noLiberties(true);
        while (!toVisit.empty()) {
            Pt curr = toVisit.top();
            toVisit.pop();
            for (const auto adj : adjacent(curr)) {
                if (outOfBounds(adj))
                    continue;
                if (getColor(adj) == getColor(curr) &&
                    visited.find(adj) == visited.end())
                {
                    toVisit.push(adj);
                    visited.insert(adj);
                } else if (getColor(adj) == Color::Empty) {
                    noLiberties = false;
                }
            }
        }
        
        if (noLiberties) {
            for (const auto& remove : visited)
                grid[remove.row][remove.col] = Color::Empty;
            return true;
        }
        return false;
    }

    void switchTurn() {
        if (turnColor == Color::Black)
            turnColor = Color::White;
        else
            turnColor = Color::Black;
    }

    public:

    Board() {
        for (auto& row : grid)
            for (auto& p : row)
                p = Color::Empty;
    }

    void display() {
        for (int i(0); i < SIZE; i++) {
            for (int j(0); j < SIZE; j++) {
                switch (getColor(Pt{i, j})) {
                    case Color::Empty:
                        cout << ".";
                        break;
                    case Color::Black:
                        cout << "#";
                        break;
                    case Color::White:
                        cout << "*";
                        break;
                }
                if (j < SIZE - 1)
                    cout << " ";
            }
            cout << endl;
        }
    }

    bool isEmpty(Pt pt) {
        return getColor(pt) == Color::Empty;
    }

    bool place(Pt pt) {
        if (!isEmpty(pt) || outOfBounds(pt))
            return false;

        grid[pt.row][pt.col] = turnColor;
        switchTurn();
        
        bool noCapture(true);
        for (const auto adj : adjacent(pt))
            if (attemptCapture(adj))
                noCapture = false;
        if (noCapture)
            attemptCapture(pt);

        return true;
    }

    vector<Pt> validMoves() {
        vector<Pt> moves;
        for (int i(0); i < SIZE; i++) {
            for (int j(0); j < SIZE; j++) {
                Pt pt = {i, j};
                if (isEmpty(pt))
                    moves.push_back(pt);
            }
        }
        return moves;
    }

    int playout() {
        while (true) {
            vector<Pt> moves = validMoves();
            if (moves.size() <= 1)
                break;
            Pt move = moves[rand() % moves.size()];
            place(move);
        }
        if (blackWins())
            return 1;
        else
            return -1;
    }

    int blackWins() {
        int blackAdv(0);
        for (auto row : grid) {
            for (auto p : row) {
                switch (p) {
                    case Color::Black:
                        blackAdv++;
                        break;
                    case Color::White:
                        blackAdv--;
                }
            }
        }
        return blackAdv > 0;
    }

    bool blackTurn() {
        return turnColor == Color::Black;
    }
};

class MCTS {
    class Node {
        public:

        Board board;
        Pt move;
        vector<unique_ptr<Node>> children;
        int visits = 0;
        double wins = 0.0;
        int playForBlack;

        Node(const Board& b, Pt m) : board(b), move(m) {}

        double UCT(int totalVisits) const {
            if (visits == 0)
                return numeric_limits<double>::infinity();
            return wins / totalVisits
                + 1.1 * sqrt(log(totalVisits) / visits);
        }

        void expand() {
            for (const auto& move : board.validMoves()) {
                Board newBoard = board;
                newBoard.place(move);
                children.push_back(
                    make_unique<Node>(newBoard, move));
            }
        }
    };

    Node* root;
    vector<Node*> path;
    int playForBlack;

    Node* select(Node* node) {
        path.clear();
        while (!node->children.empty()) {
            double bestValue(-numeric_limits<double>::infinity());
            Node* bestNode = nullptr;
            for (auto& child : node->children) {
                double value(child->UCT(node->visits + 1));
                if (value > bestValue) {
                    bestValue = value;
                    bestNode = child.get();
                }
            }
            node = bestNode;
            path.push_back(node);
        }
        return node;
    } 

    void backpropagate(int result) {
        for (const auto& node : path) {
            node->visits++;
            node->wins += result * playForBlack;
        }
    }

    public:

    MCTS(Board b) {
        root = new Node(b, Pt{-1, -1});
        if (b.blackTurn())
            playForBlack = 1;
        else
            playForBlack = -1;

    }

    Pt runMCTS(int iterations) {
        for (int i(0); i < iterations; i++) {
            Node* node = select(root);
            if (node->children.empty()) {
                node->expand();
                node = node->children[
                    rand() % node->children.size()].get();
            }
            backpropagate(node->board.playout());

            float progress = static_cast<float>(i) / iterations;
            cout << "[";
            for (int j(0); j < SIZE * 2 - 3; j++) {
                if (j < (SIZE * 2 - 3) * progress)
                    cout << "=";
                else
                    cout << " ";
            }
            std::cout << "] "
                << static_cast<int>(progress * 100)
                << "%\r";
            std::cout.flush();
        }

        if (root->children.empty())
            return Pt{-1, -1};

        Node* bestChild = root->children[0].get();
        for (const auto& child : root->children) {
            if (child->visits > bestChild->visits)
                bestChild = child.get();
        }
        return bestChild->move;
    }
};

int main() {
    Board board;
    board.display();
    while (true) {
        /*int r, c;
        do {
            cout << ": ";
            cin >> r >> c;
        } while(!board.place(Pt{r, c}));
        board.display();*/
        Pt move = (new MCTS(board))->runMCTS(12000);
        if (move.row == -1 && move.col == -1)
            return 0;
        cout << endl << "> " << move.row
             << " " << move.col << endl;
        board.place(move);
        board.display();
    }
}
