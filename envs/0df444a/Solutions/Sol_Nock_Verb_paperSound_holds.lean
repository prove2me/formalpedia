-- Prove2me | solution 1 for Nock.Verb.paperSound_holds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:41.111884+00:00
-- url     : https://prove2.me/submissions/43e15d90-e907-47ab-972a-dfa854719cef

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_iff_evalPaper
public import Theorems.Thm_Nock_Verb_run_soundP
public import Theorems.Thm_Nock_Verb_editOk_program


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution : PaperSound := by
  intro s f r hrun
  obtain ⟨fuel, h⟩ := hrun
  have hd : ∃ f', denP f' (program s f) = some r := run_soundP fuel (editOk_program s f) h
  exact (denP_iff_evalPaper s f r).1 hd
end Nock.Verb
