# Christiano Braga
# Nov. 2020
# Grammar transformation to Greibach normal form.
# The productios of a grammar are represented as a dictionary where
# each item is a set of RHS productions with the same LHS. The key is the
# LHS and the value is a list, whose elements are each RHS of the given
# LHS in the production set.

# Given a grammar G = (V, T, P, S), all symbols are strings, V is
# implemented as a list and so is T. S is a string and P is as
# described above.

import pprint
from termcolor import colored
import copy
import itertools
from copy import deepcopy

#--------------------------------------Funções Auxiliares Construídas---------------------------------------------
# retorna os conjuntos V e T de uma gramática, dado que é passado uma regra de produções P
def get_conj_V_e_T(P):
    Vl=[]
    Tl=[]
    for A in P:
        Vl.append(A)
        for producoes in P[A]:
            for simbolo in producoes:
                if simbolo != 'epsilon' :
                    if simbolo.isupper():
                        Vl.append(simbolo)
                    else:
                        Tl.append(simbolo)
    return (set(Vl),set(Tl))

#imprime uma lista de produções de uma variável em notação utilizada na disciplina  para gramáticas, dada
# uma regra de produções p, e uma variável key
def print_prod_Pedro(p,key):
    print(key+" → "+str(p[key]).replace("\"","").replace("\', ","").replace("[","").replace("]","").replace(","," | ").replace("\'",""))

#retorna em string uma lista de produções de uma variável em notação utilizada na disciplina para gramáticas, dada
# uma regra de produções p, e uma variável key
def prod_2_string(p,key):
    return key + " → " + str(p[key]).replace("\"", "").replace("\', ", "").replace("[", "").replace("]", "").replace(",",
                                                                                                              " | ").replace(
        "\'", "")+'\n'

#converte qualquer item presente neste código em string na notação utilizada na disciplina para gramáticas
def formata_LFTC(item):
    return str(item).replace("\"","").replace("\', ","").replace("[","").replace("]","").replace(","," | ").replace("\'","")

#retorna true se x estiver presente em uma lista ou conjunto A (x € A) e false caso contrário
def pertence(x,A):
    return x in A

#retorna true se a variável A for uma variável auxiliar de Remoção de recursão a esquerda
#isto é, se A for da forma "K_rr", e false caso contrário
def eh_remocao_de_recursao(A):
    return A.find("_rr")>=0

#troca a denominação de todas as variáveis auxiliares de remoção de recursão a esquerda de uma gramática
#e as substitui por caracteres maiúsculos especiais ['ẞ','Ω','Æ','∏','Œ','∆','Þ','Γ','Θ','Λ','Φ','Ξ','Ψ']
#útil para enxergar melhor "apenas batendo o olho numa gramática" se determinada variável
#é variavel auxiliar de remoção de recursão a esquerda.
def P_2_string_change_rr_letter(P):
    p=P_2_string(P)
    alternativ_alfab=['ẞ','Ω','Æ','∏','Œ','∆','Þ','Γ','Θ','Λ','Φ','Ξ','Ψ']
    p=p.replace("_rr",'§')
    repl=set()

    for i in range(len(p)):
        if (p[i]=='§'):
            repl.add(p[i-1]+'§')
    j=0
    for i in repl:
       p=p.replace(i,alternativ_alfab[j])
       j=j+1
    return p

# converte em string um conjunto de regras de produção, utilizando a notação da disciplina para gramáticas
def P_2_string(P):
    resp=''
    for prod in P:
        resp=resp+prod_2_string(P,prod)
    return resp

# imprime conjunto de regras de produção utilizando a notação da disciplina para gramáticas
def print_P(P):
    for prod in P:
        print_prod_Pedro(P,prod)

#função primitiva lisp car , útil no processamento de listas , necessaria em implementações aqui feitas
def car(l):
    return l[0]

#função primitiva lisp cdr
def cdr(l):
    return l[1:]

# verifica se um símbolo é variável de gramática (x € V), retorna true se o símbolo é maiusculo, e falso caso contrario
def eV(x):
    a=x
    if len(x)>1:
        a=x[0]
    return a.isupper()

#função primitiva lisp cons
def cons(a,b):
    A=[]
    B=[]
    if type(a)!= type([]):
        A=[a]
    else:
        A=a
    if type(b)!= type([]):
        B=[b]
    else:
        B=b
    return A+B

#retorna uma nova lista revertida
def reverseTRUE(l):
    a=[]
    for i in range(len(l)-1,-1,-1):
        a.append(l[i])
    return a
#-----------------------------------------------------------------------------------------------------------------

#--------------------------------------Funções Originais (Christiano)---------------------------------------------
def sort_variables(v):
    v_set = set(v)
    v_list = list(v_set)
    return v_list

def r_lte_s(v, p_0):
    p = copy.deepcopy(p_0)
    for a_r in v:
        for a_s in v: 
            if v.index(a_s) < v.index(a_r):
                rhs_list = p[a_r]
                for rhs in rhs_list:
                    if rhs[0] == a_s:
                        for beta in p[a_s]:
                            beta_copy = beta.copy()
                            beta_copy.extend(rhs[1:]) # beta alpha
                            p[a_r].append(beta_copy)
                        p[a_r].remove(rhs)
    return p

def left_recursion_elimination(v, p_0):
    p = copy.deepcopy(p_0)
    excluded = []
    new_p = {}
    for a_r in p:
        for i, rhs in enumerate(p[a_r]):
            if rhs[0] == a_r:
                rhs_copy = rhs.copy()
                b_r = rhs_copy[0] + "_rr"
                v = v.append(b_r)
                alpha = rhs_copy[1:]
                alpha_x = alpha.copy()
                alpha_x.append(b_r)
                new_p.update({ b_r : [alpha, alpha_x] })
                p[a_r].remove(rhs)
                excluded += a_r
    p.update(new_p)
    for a_r in excluded:
        rhs_list = copy.deepcopy(p[a_r])
        for rhs in rhs_list:
            rhs_copy = rhs.copy()
            rhs_copy.append(a_r + "_rr")
            p[a_r].append(rhs_copy)
    return p

def print_prod(p):
    for key in p.keys():
        print(colored(key, 'magenta') + colored(" → ", 'white', attrs=['bold']) + colored(" ".join(p[key][0]), 'cyan'))
        for rhs in p[key][1:]:
            print(colored(" | ", 'white', attrs=['bold']) + colored(" ".join(rhs), 'cyan'))

def begin_with_terminal(p):
    pass

def terminal_followed_by_word_of_variables(p):
    pass
#-----------------------------------------------------------------------------------------------------------------

#---------------------------------Novas Funções (Etapas 5 e 6 da FNG)---------------------------------------------
#afim de melhor organização, as funções correspondentes as etapas 5 e 6 da FNG (FNG 5 e FNG 6 respectvmt.)
#foram implementadas em novas funções :
#       begin_with_terminal2(Vold,Pold) {correspondente a FNG 5}  e
#       terminal_followed_by_word_of_variables2(Pold,Vold) {correspondente a FNG 6}
#pois viu-se a necessidade de adicionar parâmetros as mesmas, que não estavam presentes nas funções protótipo
#originais deste exercício, isto é, foi necessário passar como parâmetro, em ambas, o conjunto V de cada gramática
#para verificações pertinentes as etapas
#consequentemente, na função original que realiza os testes (mk_example(ex_num, v_0, p_0))
#  foi atualizada a chamada das funções nestas etapas (5 e 6) para as funções a seguir criadas

#Realiza a etapa 6 da FNG que faz com que todas as regras de produção sejam formadas por um terminal
#seguida de palavra de variaveis, passando como parametro (Pold) que é um conjunto de regras de produções
#que tenha passado pela etapa 5, e (Vold) o conjunto V com as variaveis pertinentes o conjunto Pold
# e retorna um novo conjunto de regras de produção convertido na etapa 6.
def terminal_followed_by_word_of_variables2(Pold,Vold):
    V=deepcopy(Vold)
    P=deepcopy(Pold)
    i=1
    #print(colored(P_2_string(P), color='yellow'))
    for A in V:
        neu=[]
        neue=[]
        producoes_A=deepcopy(P[A])
        for producao in producoes_A:
            primeiro_simbolo=producao[0]
            demais_simbolos=producao[1:]
            nova_prod=producao
            if eV(primeiro_simbolo):#se é variavel...
                print("Houve erro em alguma etapa,  chegou-se até etapa 6 com variavel como primeiro simbolo")
                break
            else: # se nao e var , tá tudo ok
                posicao_troca=[]
                for simbolo in range(len(demais_simbolos)):
                    if not eV(demais_simbolos[simbolo]):
                        nova_prod=['$$$$'+demais_simbolos[simbolo]+'$$']
                        posicao_troca.append(simbolo)
                if posicao_troca!=[]:#
                    DS=deepcopy(demais_simbolos)
                    for subst in posicao_troca:
                        simbolo_velho=DS[subst]
                        DS[subst]='Ω_'+str(i)
                        P['Ω_'+str(i)]=[[simbolo_velho]]
                        i=i+1
                    nova_prod=[primeiro_simbolo]+DS

            neu.append(nova_prod)
        P[A] = neu
    return P


#Realiza a etapa 5 da FNG que faz com que todas as regras de produção sejam formadas por um terminal
#no início. passando como parametro (Pold) que é um conjunto de regras de produções
#que tenha passado pela etapa 4, e (Vold) o conjunto V com as variaveis pertinentes o conjunto Pold
# e retorna um novo conjunto de regras de produção convertido na etapa 5.
def begin_with_terminal2(Vold,Pold):#FNG+5
    V=deepcopy(Vold)
    P=deepcopy(Pold)
    #ETAPA 1 REMOVENDO A_r→A_s α
    trocas=[]
    manter=[]
    Vr=deepcopy(V)
    Vr=reverseTRUE(Vr)
    #TROCANDO PRODUCOES NORMAIS
    for A_r in Vr:
        producoes_A_r=deepcopy(P[A_r])
        if not eh_remocao_de_recursao(A_r):
            neu=[]
            for producao in producoes_A_r:
                if not eV(producao[0]) :# se é Variavel
                    neu.append(producao)
                else:
                    mesclaveis=P[producao[0]]
                    a_Mes=producao[1:]
                    for M in mesclaveis:
                        neu.append(M+a_Mes)
            P[A_r]=neu
    #TROCANDO PRODUÇÕES AUXILIARES DE REMOÇÃO DE RECURSÃO ß ("_rr")
    for A_r in Vr:
        producoes_A_r = deepcopy(P[A_r])
        if  eh_remocao_de_recursao(A_r):
            neu = []
            for producao in producoes_A_r:
                if not eV(producao[0]):
                    neu.append(producao)
                else:
                    mesclaveis = P[producao[0]]
                    a_Mes = producao[1:]
                    for M in mesclaveis:
                        neu.append(M + a_Mes)
            P[A_r] = neu

    return P
#-----------------------------------------------------------------------------------------------------------------



#Função original que realiza os testes das gramáticas, com pequenas alterações
#1. alterada a chamada para os métodos que realizam as etapas 5 e 6 para os novos métodos implementados
#2. Adicionada uma gramática de exemplo para testes da etapa 6 da FNG, esta gramática de exemplo
#   passou por todas as etapas da FNG até a etapa 5, e contém algumas produções da forma A → aφ
#   onde φ € (V u T)* , isto é, φ é formada por símbolos terminais e variáveis, por exemplo
#   nesta gramática de exemplo, foi inserida uma produção 'A →bCBaaAACA_rr'
#   ela deve ser trocada por 'A →bCBΩ_1Ω_2AACA_rr' e devem ser inseridas novas produções 'Ω_1→a' e 'Ω_2→a'
#   onde Ω_1 e Ω_2 são variáveis
def mk_example(ex_num, v_0, p_0):
    pp = pprint.PrettyPrinter(indent=4)
    print(colored("Example " + str(ex_num), attrs=['bold']))
    print("Original production set.")
    print_prod(p_0)
    # gramática de teste para a etapa 6 da FNG
    teste_FNG6={   'A': [   ['b', 'C'],
             ['a', 'A', 'C'],
             ['b', 'C', 'A_rr'],
             ['a', 'A', 'C', 'A_rr']],
    'A_rr': [   ['b', 'A', 'C'],
                ['b', 'C', 'B', 'A', 'b','b','A', 'C'],
                ['a', 'A', 'C', 'B', 'A', 'A', 'C'],
                ['b', 'C', 'A_rr', 'B', 'A', 'A', 'C'],
                ['a', 'A', 'C', 'A_rr', 'B', 'A', 'A', 'C'],
                ['a', 'A', 'A', 'C'],
                ['b', 'A', 'C', 'A_rr'],# nesta gramatica já passada pela fase 5 da FNG
                ['b', 'C', 'B', 'a','a','A', 'A', 'C', 'A_rr'],#<- foi inserido (propositadamente afim de testar)
                ['a', 'A', 'C', 'B', 'A', 'A', 'C', 'A_rr'],#  um simbolo final no meio da palavra de variaveis
                ['b', 'C', 'A_rr', 'B', 'A', 'A', 'C', 'A_rr'],
                ['a', 'A', 'C', 'A_rr', 'B', 'A', 'A', 'C', 'A_rr'],
                ['a', 'A', 'A', 'C', 'A_rr']],
    'B': [   ['b'],
             ['b', 'C', 'B', 'A'],
             ['a', 'A', 'C', 'B', 'A'],
             ['b', 'C', 'A_rr', 'B', 'A'],
             ['a', 'A', 'C', 'A_rr', 'B', 'A'],
             ['a', 'A']],
    'C': [   ['b', 'C', 'B'],
             ['a', 'A', 'C', 'B'],
             ['b', 'C', 'A_rr', 'B'],
             ['a', 'A', 'C', 'A_rr', 'B'],
             ['a']]}
    V_teste_FNG6=["A_rr","B","C"]
    for i, v in enumerate(list(itertools.permutations(v_0))):
        print(colored("Example "+ str(ex_num) + "." + str(i), 'green', attrs=['bold']))
        
        # First step: grammar simplification
        print(colored("Second step: sort variables", 'blue'))
        v = list(v)
        pp.pprint(v)

        # Third and fourth steps: production set transformation to
        # A_r → A_s α, where r ≤ s and removal of productions of the form
        # Ar → Arα.
        
        print(colored("Production set transformation to A_r → A_s α, where r ≤ s.", 'blue'))
        p_i = r_lte_s(v, p_0)
        print_prod(p_i)
        print(colored("Production set elimination of A_r → A_r α.", 'blue'))    
        p_i = left_recursion_elimination(v, p_i)
        print_prod(p_i)
        print(colored("Each production begining with a terminal.", 'grey'))
        p_i=begin_with_terminal2(v,p_i)
        #pp.pprint(p_i)
        #print_P(p_i)
        print(colored(P_2_string(p_i),color='blue'))
        print(colored("Each production begining with a terminal followed by a word of variables.", 'grey'))
        print(colored(P_2_string(p_i),color='grey'))
        p_i = terminal_followed_by_word_of_variables2(p_i,v)
        print(colored("TESTE da FNG-6 : Gramática com algumas produções da forma A->aK \n onde K pertence a (V u T)* \n gramática original na FNG-5:", 'red'))
        print(colored(P_2_string(teste_FNG6),color='red'))
        print(colored("Each production begining with a terminal followed by a word of variables.\n gramática anterior convertida na FNG-6", 'red'))
        p_FNG6Test = terminal_followed_by_word_of_variables2(teste_FNG6,["A_rr","B","C"])
        print(colored(P_2_string(p_FNG6Test),color='red'))

if __name__ == "__main__":
    print(colored("Examples of transformations from CFG to Greibach normal form", attrs=['bold']))

    ### Example 1
    v_0 = ["A", "S"]
    t = ["a", "b"]
    p_0 = { "S" : [["A", "A"], ["a"]], "A" : [["S", "S"], ["b"]] }
    s  = "S"
    mk_example(1, v_0, p_0)

    ### Example 2
    v1 = ["A", "B", "C"]
    t1 = ["a", "b"]
    p1 = { "A" : [["B", "C"]], "B" : [["C", "A"], ["b"]], "C" : [["A", "B"], ["a"]] }
    s1  = "A"
    mk_example(2, v1, p1)
    
