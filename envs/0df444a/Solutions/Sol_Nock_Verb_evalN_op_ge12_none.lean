-- Prove2me | solution 1 for Nock.Verb.evalN_op_ge12_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:14.733226+00:00
-- url     : https://prove2.me/submissions/75d1a69a-53fd-4c97-9630-ae0a5ec00149

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (f : Nat) (s tail : Noun) (op : Nat) (h : 12 ≤ op) :
    evalN f s (.cell (.atom op) tail) = none := by
  cases f with
  | zero => rfl
  | succ ff =>
      simp only [evalN]
      split <;> first | rfl | omega
end Nock.Verb
