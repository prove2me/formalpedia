-- Prove2me | solution 1 for Nock.Verb.deterministic_Trace_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:15.666286+00:00
-- url     : https://prove2.me/submissions/6da81888-1311-41d9-8ece-b07d0ad467af

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_selStep_deterministic_Trace
public import Theorems.Thm_Nock_Verb_consistent_iff_selStep
public import Theorems.Thm_Nock_Verb_strictSelect_dfs


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOf F T1) (h2 : TraceOf F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 :=
  selStep_deterministic_Trace strictSelect_dfs
    ⟨h1.1, (consistent_iff_selStep T1).1 h1.2⟩
    ⟨h2.1, (consistent_iff_selStep T2).1 h2.2⟩ hn1 hn2
end Nock.Verb
