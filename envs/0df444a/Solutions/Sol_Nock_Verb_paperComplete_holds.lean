-- Prove2me | solution 1 for Nock.Verb.paperComplete_holds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:04.371961+00:00
-- url     : https://prove2.me/submissions/c35876ed-c4ba-4a02-9673-07decda2f446

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_run_completeP
public import Theorems.Thm_Nock_Verb_denP_iff_evalPaper
public import Theorems.Thm_Nock_Verb_editOk_program


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution : PaperComplete := by
  intro s f r hev
  obtain ⟨g, hg⟩ := (denP_iff_evalPaper s f r).2 hev
  obtain ⟨N, hN⟩ := run_completeP (editOk_program s f) ⟨g, hg⟩
  exact ⟨N, hN⟩
end Nock.Verb
