-- Prove2me | solution 1 for Nock.Verb.eval_value_iff_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:09.713674+00:00
-- url     : https://prove2.me/submissions/1b43c8f5-c04b-4ec5-87fd-b73d5ae9ebf1

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_eval_succ

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {n : Nat} {v : Verb} {r : Noun} :
    eval n v = .value r ↔ run n v = some r := by
  induction n generalizing v with
  | zero => simp [eval, run]
  | succ n ih =>
      rw [eval_succ, run]
      cases hnv : next v with
      | some v' => exact ih
      | none =>
          simp only [haltOutcome, result]
          by_cases ht : v.isTerminal
          · simp [ht]
          · simp [ht]
end Nock.Verb
