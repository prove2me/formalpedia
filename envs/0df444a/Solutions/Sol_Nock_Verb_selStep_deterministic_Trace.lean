-- Prove2me | solution 1 for Nock.Verb.selStep_deterministic_Trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:53.252732+00:00
-- url     : https://prove2.me/submissions/302e848f-05a7-40e7-b986-2bb92ab0aaa6

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_Step_det
public import Theorems.Thm_Nock_Verb_trace_unique_of_det
public import Theorems.Thm_Nock_Verb_SelStep_det


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {lt : Nat → Nat → Prop} (hs : StrictSelect lt)
    {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOfR (SelStep lt) F T1) (h2 : TraceOfR (SelStep lt) F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 :=
  trace_unique_of_det (R := SelStep lt)
    (fun {a b b'} (hab : SelStep lt a b) (hab' : SelStep lt a b') => SelStep.det hs hab hab')
    T1 T2 h1.2 h2.2 (h1.1.trans h2.1.symm) (by omega)
end Nock.Verb
