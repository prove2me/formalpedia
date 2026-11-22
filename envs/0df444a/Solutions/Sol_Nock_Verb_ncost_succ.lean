-- Prove2me | solution 1 for Nock.Verb.ncost_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:45.04541+00:00
-- url     : https://prove2.me/submissions/28333875-9674-4f7b-80b2-659112e50b26

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_evalN_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n : Nat} {a b : Noun} {r : Noun}
    (hb : evalN n a b = some r) : ncost (n + 1) a b = ncost n a b := by
  induction n, a, b using evalN.induct generalizing r <;>
    simp_all only [evalN, ncost, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq, reduceCtorEq] <;>
    grind only [evalN_succ]
end Nock.Verb
