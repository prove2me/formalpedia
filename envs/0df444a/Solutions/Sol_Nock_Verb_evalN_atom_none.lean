-- Prove2me | solution 1 for Nock.Verb.evalN_atom_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:38.994156+00:00
-- url     : https://prove2.me/submissions/17429d9a-c5c6-4292-89bd-5b0bf07f3199

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
theorem _root_.solution (f : Nat) (s : Noun) (k : Nat) : evalN f s (.atom k) = none := by
  cases f <;> simp [evalN]
end Nock.Verb
