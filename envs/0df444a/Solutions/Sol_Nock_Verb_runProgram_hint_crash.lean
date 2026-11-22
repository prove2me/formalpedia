-- Prove2me | solution 1 for Nock.Verb.runProgram_hint_crash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:30.226636+00:00
-- url     : https://prove2.me/submissions/ccfb46aa-bfb7-4d87-a13b-a57bc0632a05

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_next_hintProg_none

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (subj n2 : Noun) :
    ∀ fuel, runProgram fuel subj (.cell (.atom 11) n2) = none := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ f =>
      unfold runProgram
      rw [run, next_hintProg_none subj n2]
      simp [result, program, isTerminal, ofNoun, Action.isNull]
end Nock.Verb
