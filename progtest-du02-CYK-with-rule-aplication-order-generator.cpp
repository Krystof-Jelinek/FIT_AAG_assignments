#ifndef __PROGTEST__
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iomanip>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <vector>

using namespace std;
using Symbol = char;
using Word = std::vector<Symbol>;

struct Grammar {
    std::set<Symbol> m_Nonterminals;
    std::set<Symbol> m_Terminals;
    std::vector<std::pair<Symbol, std::vector<Symbol>>> m_Rules;
    Symbol m_InitialSymbol;
};
#endif

struct coordinates{
    int x;
    int y;

    coordinates(){
        x = -1;
        y = -1;
    }

    coordinates(int x1, int y1){
        x = x1;
        y = y1;
    }
};

struct nont_rule {
    Symbol nont;
    int rule_index;
    coordinates sons[2];

    nont_rule(){
        rule_index = -1;
        nont = '#';
    }

    nont_rule(char c, int index, coordinates & first, coordinates & second){
        nont = c;
        rule_index = index;
        sons[0] = first;
        sons[1] = second;
    }
};

bool operator<(const nont_rule& lhs, const nont_rule& rhs) {
    return lhs.nont < rhs.nont;
}

struct CYK_cell {
    set<nont_rule> possible_nonts;

    bool find_inicial(char c){
        coordinates dummy;
        nont_rule tmp(c,-5,dummy, dummy);

        if (possible_nonts.find(tmp) == possible_nonts.end()){
            return false;
        }
        return true;
    }

    nont_rule find_nont_rule(char c){
        coordinates dummy;
        nont_rule tmp(c,-5,dummy, dummy);

        auto ret = possible_nonts.find(tmp);
        
        if(ret == possible_nonts.end()){
            throw std::logic_error("This should not happen");
        }
        return (*ret);
    }

    void find_all_possible_nonts(const Grammar & grammar, Symbol c){
        int cur_index = 0;
        coordinates dummy;

        for(auto itr = grammar.m_Rules.begin(); itr != grammar.m_Rules.end(); itr++){
            if((!(*itr).second.empty()) && ((*itr).second[0] == c)){
                possible_nonts.insert(nont_rule(itr->first, cur_index, dummy,dummy));
            }
            cur_index++;
        }
    }

    void find_all_possible_nonts(const Grammar & grammar, const Word & duo, coordinates & first_cell, coordinates & second_cell){
        int cur_index = 0;
        for(auto itr = grammar.m_Rules.begin(); itr != grammar.m_Rules.end(); itr++){
            if((!itr->second.empty()) && ((*itr).second.front() == duo.front()) && ((*itr).second.back() == duo.back())){
                possible_nonts.insert(nont_rule(itr->first, cur_index, first_cell, second_cell));
            }
            cur_index++;
        }
    }
};

set<Word> carthesian_product(CYK_cell & first, CYK_cell & second){
    set<Word> res;

    for(auto itr = first.possible_nonts.begin() ; itr != first.possible_nonts.end(); itr++){
        for(auto itr2 = second.possible_nonts.begin(); itr2 != second.possible_nonts.end(); itr2++){
            res.insert({itr->nont , itr2->nont});
        }
    }
    return res;
}

struct CYK_table {
    
    vector<vector<CYK_cell>> table;
    int max_index;
    Grammar grammar;
    Word word;
    bool can_generate_E;
    int E_rule_index;
    
    CYK_table(int word_length, const Grammar & grammar, const Word & word){
        table.resize(word_length, std::vector<CYK_cell>(word_length));
        max_index = word_length -1;
        this->grammar = grammar;
        this->word = word;
        E_rule_index = -1;
        can_generate_E = generate_E();
    }

    bool generate_E(){
        int index = 0;

        for(auto itr = grammar.m_Rules.begin(); itr!= grammar.m_Rules.end(); itr++){
            if(itr->second.empty()){
                E_rule_index = index;
                return true;
            }
            index++;
        }
        return false;
    }

    void fill_first_diagonal(){
        int index = max_index;

        for(int i = 0; i != max_index + 1; i++, index--){
            table[index][i].find_all_possible_nonts(grammar, word[i]);
        }

    }

    void fill_cell(int ancor_x, int ancor_y){
        int slider_x = max_index - ancor_y;
        int slider_y = ancor_y + 1;

        while(slider_x != ancor_x){

            set<Word> carthese = carthesian_product(table[slider_x][ancor_y], table[ancor_x][slider_y]);

            for(auto itr = carthese.begin(); itr!= carthese.end(); itr++){
                coordinates first(slider_x, ancor_y);
                coordinates second(ancor_x, slider_y);
                table[ancor_x][ancor_y].find_all_possible_nonts(grammar, (*itr), first, second);
            }

            slider_x--;
            slider_y++;
        }

    }

    void fill_diagonal(int start_row_index){
        int second_index = 0;

        while(start_row_index >= 0){
            fill_cell(start_row_index, second_index);
            start_row_index--;
            second_index++;
        }
    }

    void fill_table(){
        fill_first_diagonal();

        int index = max_index -1;
        
        while(index >= 0){
            fill_diagonal(index);
            index--;
        }
    }

    std::vector<size_t> generate_rec(vector<size_t> & output, coordinates & cur_coords, char c){
        nont_rule tmp = table[cur_coords.x][cur_coords.y].find_nont_rule(c);

        output.push_back(tmp.rule_index);
        
        if(tmp.sons[0].x != -1){
            generate_rec(output, tmp.sons[0], grammar.m_Rules[tmp.rule_index].second.front());
            generate_rec(output, tmp.sons[1], grammar.m_Rules[tmp.rule_index].second.back());
        }

        return output;

    }

    std::vector<size_t> generate(){
        vector<size_t> ret;

        if(!table[0][0].find_inicial(grammar.m_InitialSymbol)){
            return ret;
        }

        coordinates start(0,0);
        return generate_rec(ret, start, grammar.m_InitialSymbol);
    }
};

std::vector<size_t> trace(const Grammar& grammar, const Word& word){
    CYK_table cyk_table(word.size(), grammar, word);

    vector<size_t> ret;

    if(word.empty()){
        if(cyk_table.can_generate_E == true){
            ret.push_back(cyk_table.E_rule_index);
        }
        return ret;
    }

    cyk_table.fill_table();
    return cyk_table.generate();  
}

#ifndef __PROGTEST__
int main()
{

    
    Grammar g0{
        {'A', 'B', 'C', 'S'},
        {'a', 'b'},
        {
            {'S', {'A', 'B'}},
            {'S', {'B', 'C'}},
            {'A', {'B', 'A'}},
            {'A', {'a'}},
            {'B', {'C', 'C'}},
            {'B', {'b'}},
            {'C', {'A', 'B'}},
            {'C', {'a'}},
        },
        'S'};

    trace(g0, {'b', 'a', 'a', 'b', 'a'}) == std::vector<size_t>({0, 2, 5, 3, 4, 6, 3, 5, 7});
    trace(g0, {'b'}) == std::vector<size_t>({});
    trace(g0, {'a'}) == std::vector<size_t>({});
    trace(g0, {}) == std::vector<size_t>({});
    trace(g0, {'a', 'a', 'a', 'a', 'a'}) == std::vector<size_t>({1, 4, 6, 3, 4, 7, 7, 7, 7});
    trace(g0, {'a', 'b'}) == std::vector<size_t>({0, 3, 5});
    trace(g0, {'b', 'a'}) == std::vector<size_t>({1, 5, 7});
    trace(g0, {'c', 'a'}) == std::vector<size_t>({});

    Grammar g1{
        {'A', 'B'},
        {'x', 'y'},
        {
            {'A', {}},
            {'A', {'x'}},
            {'B', {'x'}},
            {'A', {'B', 'B'}},
            {'B', {'B', 'B'}},
        },
        'A'};

    trace(g1, {}) == std::vector<size_t>({0});
    trace(g1, {'x'}) == std::vector<size_t>({1});
    trace(g1, {'x', 'x'}) == std::vector<size_t>({3, 2, 2});
    trace(g1, {'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 2, 2, 2});
    trace(g1, {'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 2, 2, 2, 2});
    trace(g1, {'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 2, 2, 2, 2, 2});
    trace(g1, {'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2});
    trace(g1, {'x', 'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2});
    trace(g1, {'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2});
    trace(g1, {'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2});

    Grammar g2{
        {'A', 'B'},
        {'x', 'y'},
        {
            {'A', {'x'}},
            {'B', {'x'}},
            {'A', {'B', 'B'}},
            {'B', {'B', 'B'}},
        },
        'B'};

    trace(g2, {}) == std::vector<size_t>({});
    trace(g2, {'x'}) == std::vector<size_t>({1});
    trace(g2, {'x', 'x'}) == std::vector<size_t>({3, 1, 1});
    trace(g2, {'x', 'x', 'x'}) == std::vector<size_t>({3, 3, 1, 1, 1});


    Grammar g3{
        {'A', 'B', 'C', 'D', 'E', 'S'},
        {'a', 'b'},
        {
            {'S', {'A', 'B'}},
            {'S', {'S', 'S'}},
            {'S', {'a'}},
            {'A', {'B', 'S'}},
            {'A', {'C', 'D'}},
            {'A', {'b'}},
            {'B', {'D', 'D'}},
            {'B', {'b'}},
            {'C', {'D', 'E'}},
            {'C', {'b'}},
            {'C', {'a'}},
            {'D', {'a'}},
            {'E', {'S', 'S'}},
        },
        'S'};

    trace(g3, {}) == std::vector<size_t>({});
    trace(g3, {'b'}) == std::vector<size_t>({});
    trace(g3, {'a', 'b', 'a', 'a', 'b'}) == std::vector<size_t>({1, 2, 0, 3, 7, 1, 2, 2, 7});
    trace(g3, {'a', 'b', 'a', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'a'}) == std::vector<size_t>({1, 1, 0, 4, 8, 11, 12, 0, 5, 6, 11, 11, 0, 4, 9, 11, 7, 11, 7, 2, 2});

    Grammar g4{
        {'A', 'B', 'C', 'S'},
        {'a', 'b'},
        {
            {'S', {'A', 'B'}},
            {'S', {'B', 'C'}},
            {'A', {'B', 'A'}},
            {'A', {'a'}},
            {'B', {'C', 'C'}},
            {'B', {'b'}},
            {'C', {'A' , 'B'}},
            {'C', {'a'}},
        },
        'S'};

vector<size_t> tmp = trace(g4, {'b' , 'a' , 'a', 'b', 'a'});

return 0;

}


#endif

