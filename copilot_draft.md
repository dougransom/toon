Got it — here’s the **complete all‑in‑one Markdown document** with everything: the TOON Prolog implementation, DCG parser, DCG emitter, and inline DSL example. You can copy this straight into a file (e.g. `docs/toon.md`) and commit it to Git.

---

# TOON Implementation in Prolog (with `reif` and `dif`)

This document describes a complete Prolog implementation of TOON, using **reification (`if_/3`, `=(X,Y,Truth)`, `memberd_t/3`)** and **disequality (`dif/2`)** where appropriate. It also includes a mechanism to inline TOON directly in a Prolog source file to efficiently represent repeated rules with the same principal functor (e.g., `f(1). f(2). f(3). f(10).`).

---

## Module Overview

- **Parsing TOON** into Prolog terms using DCGs.  
- **Encoding TOON** back from Prolog terms.  
- **Path lookup** (`toon_get/3`) for nested structures.  
- **Inline Prolog evaluation** (`toon_inline_eval/2`).  
- **Normalization** with reified equality.  
- **Inline DSL**: quasi‑quotation + macro expansion to generate repeated rules at compile time.

---

## Core Module (`toon.pl`)

```prolog
:- module(toon,
    [
        toon_read/2,
        toon_read_file/2,
        toon_write/2,
        toon_write_file/2,
        toon_get/3,
        toon_inline_eval/2,
        toon_normalize/2
    ]).

:- use_module(library(dif)).

% Reified shims (for SWI if not on Scryer)
:- if(\+ current_predicate(if_/3)).
if_(Cond_1, Then, Else) :- call(Cond_1, T), ( T == true -> call(Then) ; call(Else) ).
=(X,Y,Truth) :- ( X = Y -> Truth = true ; Truth = false ).
memberd_t(Elem, List, Truth) :-
    (   memberchk(Elem, List) -> Truth = true
    ;   ( nonvar(List), \+ member(Elem, List) -> Truth = false
        ;  Truth = false ) ).
:- endif.

% --- Public API ---

toon_read(Codes, Term) :- phrase(toon_doc(Term), Codes), !.

toon_read_file(File, Term) :-
    setup_call_cleanup(
        open(File, read, In),
        ( read_string(In, _, S),
          string_codes(S, Codes),
          toon_read(Codes, Term)
        ),
        close(In)).

toon_write(Term, Codes) :- phrase(toon_emit_doc(Term, 0), Codes).

toon_write_file(Term, File) :-
    toon_write(Term, Codes),
    setup_call_cleanup(
        open(File, write, Out),
        format(Out, "~s", [Codes]),
        close(Out)).

toon_get(DB, Path, Value) :- toon_get_(DB, Path, Value).

toon_inline_eval(prolog(Term), Result) :-
    findall(Term, Term, Solutions),
    memberd_t(_, Solutions, Truth),
    if_(=(Truth, true),
        (Result = Solutions),
        (Result = false)).
toon_inline_eval(_, false).

toon_normalize(Term0, Term) :-
    if_(=(Term0, true),  (Term = true),
    if_(=(Term0, false), (Term = false),
    if_(=(Term0, null),  (Term = null),
        normalize_compound(Term0, Term)))).

normalize_compound(Map0, Map) :-
    ( is_dict(Map0) ->
        Map = Map0
    ; Map0 =.. [Type|Args],
      maplist(toon_normalize, Args, NArgs),
      Map =.. [Type|NArgs]
    ).

% Path navigation
toon_get_(Value, [], Value).
toon_get_(Dict, [Key|Rest], Value) :-
    is_dict(Dict), !,
    (  get_dict(Key, Dict, Next)
    -> toon_get_(Next, Rest, Value)
    ;  dict_pairs(Dict, _, Pairs),
       pairs_keys(Pairs, Keys),
       forall(member(K, Keys), dif(K, Key)),
       fail
    ).
toon_get_(List, [Idx|Rest], Value) :-
    is_list(List), integer(Idx), Idx >= 0, !,
    nth0(Idx, List, Next),
    toon_get_(Next, Rest, Value).
```

---

## DCG Parser

```prolog
% A TOON document is either a mapping (dict) or a list.
toon_doc(Term) --> blanks, toon_node(0, Term), blanks.

% Node at given indentation level
toon_node(Indent, Term) -->
    toon_mapping(Indent, Term)
  ; toon_list(Indent, Term)
  ; toon_scalar(Term)
  ; toon_inline_prolog(Indent, Term).

% Mapping: lines of "key: value"
toon_mapping(Indent, Dict) -->
    toon_kv_lines(Indent, Pairs),
    { dict_create(Dict, toon, Pairs) }.

toon_kv_lines(Indent, [K-V|Rest]) -->
    indent(Indent),
    key(K), ":", opt_space,
    ( toon_node(Indent+2, V)
    ; toon_scalar(V)
    ),
    eol,
    ( toon_kv_lines(Indent, Rest)
    ; { Rest = [] } ).

% List: lines starting with "- "
toon_list(Indent, List) -->
    toon_list_lines(Indent, List),
    { List \= [] }.

toon_list_lines(Indent, [Item|Rest]) -->
    indent(Indent), "- ",
    ( toon_node(Indent+2, Item)
    ; toon_scalar(Item)
    ),
    eol,
    ( toon_list_lines(Indent, Rest)
    ; { Rest = [] } ).

% Scalars
toon_scalar(String) --> quoted_string(String), !.
toon_scalar(Bool)   --> bool(Bool), !.
toon_scalar(null)   --> "null", !.
toon_scalar(Number) --> number(Number), !.
toon_scalar(Atom)   --> bare_atom(Atom).

% Inline Prolog
toon_inline_prolog(Indent, prolog(Term)) -->
    indent(Indent), "prolog:", opt_space, prolog_term(Term), eol.
toon_inline_prolog(Indent, prolog(Term)) -->
    indent(Indent), "prolog|", eol,
    prolog_block_lines(Lines),
    indent(Indent), "|", eol,
    { atomic_list_concat(Lines, ' ', Text),
      read_term_from_atom(Text, Term, [variable_names(_), syntax_errors(error)]) }.

prolog_block_lines([L|Ls]) -->
    opt_space, prolog_raw_line(L), eol,
    ( prolog_block_lines(Ls) ; { Ls = [] } ).

prolog_raw_line(Line) -->
    string_without("\n", Chars),
    { string_codes(Line, Chars) }.

prolog_term(Term) -->
    string_without("\n", Codes),
    { string_codes(S, Codes),
      read_term_from_atom(S, Term, [variable_names(_), syntax_errors(error)]) }.

% Lexical helpers
eol --> "\n".
opt_space --> ( " " ; "" ).

indent(0) --> "".
indent(N) --> { N>0 }, " ", indent(N1), { N1 is N-1 }.

key(Key) --> bare_atom(Key).

bare_atom(Atom) -->
    bare_chars(Cs),
    { Cs \= [], string_codes(S, Cs),
      atom_string(Atom, S) }.

bare_chars([C|Cs]) --> bare_char(C), bare_chars(Cs).
bare_chars([])     --> "".

bare_char(C) --> [C], { \+ code_type(C, space), C \= 0':, C \= 0'-, C \= 0'| }.

quoted_string(String) -->
    "\"", qchars(Cs), "\"",
    { string_codes(String, Cs) }.

qchars([C|Cs]) --> qchar(C), qchars(Cs).
qchars([])     --> "".
qchar(C) --> [C], { C \= 0'\" }.

number(N) -->
    signed_digits(Cs),
    { string_codes(S, Cs),
      number_string(N, S) }.

signed_digits([0'-|Ds]) --> "-", digits(Ds).
signed_digits(Ds)       --> digits(Ds).

digits([D|Ds]) --> digit(D), digits(Ds).
digits([])     --> "".
digit(D) --> [D], { code_type(D, digit) }.

bool(true)  --> "true".
bool(false) --> "false".
```

---

## DCG Emitter

```prolog
% Emit a TOON document
toon_emit_doc(Term, Indent) -->
    toon_emit_node(Term, Indent), "\n".

% Dispatch based on term type
toon_emit_node(Dict, Indent) --> { is_dict(Dict) }, !, toon_emit_dict(Dict, Indent).
toon_emit_node(List, Indent) --> { is_list(List) }, !, toon_emit_list(List, Indent).
toon_emit_node(prolog(Term), Indent) --> !,
    indent_codes(Indent), "prolog: ", prolog_emit_line(Term).
toon_emit_node(String, _) --> { string(String) }, !,
    "\"", string_codes(String), "\"