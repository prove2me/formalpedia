-- Prove2me | solution 1 for Nock.Verb.evalProgram_hint_crash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:30.646707+00:00
-- url     : https://prove2.me/submissions/8daef1e1-65bf-4fec-98a7-cb57d7cdfd80

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_next_hintProg_none
public import Theorems.Thm_Nock_Verb_eval_succ
public import Theorems.Thm_Nock_Verb_haltOutcome_crash


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (subj n2 : Noun) :
    evalProgram 1 subj (.cell (.atom 11) n2) = .crash := by
  unfold evalProgram
  rw [eval_succ, next_hintProg_none subj n2]
  exact haltOutcome_crash rfl
end Nock.Verb
