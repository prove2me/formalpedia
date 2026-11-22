-- Prove2me | solution 1 for Nock.Verb.hintComplete_holds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:44.237777+00:00
-- url     : https://prove2.me/submissions/0aea5df3-46d4-4767-921f-bedb5a35fbbf

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_run_completeN
public import Theorems.Thm_Nock_Verb_den_iff_evalN
public import Theorems.Thm_Nock_Verb_editOk_program


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution : HintComplete := by
  intro s f r hev
  obtain ⟨g, hg⟩ := (den_iff_evalN s f r).2 hev
  obtain ⟨N, hN⟩ := run_completeN (editOk_program s f) ⟨g, hg⟩
  exact ⟨N, hN⟩
end Nock.Verb
