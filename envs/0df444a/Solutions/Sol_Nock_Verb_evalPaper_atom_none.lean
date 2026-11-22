-- Prove2me | solution 1 for Nock.Verb.evalPaper_atom_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:02.874588+00:00
-- url     : https://prove2.me/submissions/1fdce38e-5d49-47e6-9fac-aa0da70ee8ea

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
theorem _root_.solution (f : Nat) (s : Noun) (k : Nat) :
    evalPaper f s (.atom k) = none := by
  cases f <;> simp [evalPaper]
end Nock.Verb
