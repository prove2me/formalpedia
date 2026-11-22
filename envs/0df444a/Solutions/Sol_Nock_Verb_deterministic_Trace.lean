-- Prove2me | solution 1 for Nock.Verb.deterministic_Trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:52.791224+00:00
-- url     : https://prove2.me/submissions/75057327-5d12-4584-80f3-677d851c5001

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_trace_unique

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOf F T1) (h2 : TraceOf F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 :=
  trace_unique T1 T2 h1.2 h2.2 (h1.1.trans h2.1.symm) (by omega)
end Nock.Verb
