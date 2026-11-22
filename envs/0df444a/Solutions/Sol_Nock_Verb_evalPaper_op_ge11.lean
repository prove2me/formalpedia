-- Prove2me | solution 1 for Nock.Verb.evalPaper_op_ge11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:11.464705+00:00
-- url     : https://prove2.me/submissions/f58ec1b7-636c-441b-a527-fcc4fbb858a8

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (f : Nat) (s tail : Noun) (op : Nat) (h : 11 ≤ op) :
    evalPaper f s (.cell (.atom op) tail) = none := by
  cases f with
  | zero => rfl
  | succ ff =>
      simp only [evalPaper]
      split <;> first | rfl | omega
end Nock.Verb
