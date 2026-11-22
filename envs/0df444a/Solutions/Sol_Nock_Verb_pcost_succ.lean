-- Prove2me | solution 1 for Nock.Verb.pcost_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:15.794929+00:00
-- url     : https://prove2.me/submissions/9ff51b84-a679-4680-8b5b-32c2f971151c

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_evalPaper_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n : Nat} {a b : Noun} {r : Noun}
    (hb : evalPaper n a b = some r) : pcost (n + 1) a b = pcost n a b := by
  induction n, a, b using evalPaper.induct generalizing r <;>
    simp_all only [evalPaper, pcost, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq, reduceCtorEq] <;>
    grind only [evalPaper_succ]
end Nock.Verb
