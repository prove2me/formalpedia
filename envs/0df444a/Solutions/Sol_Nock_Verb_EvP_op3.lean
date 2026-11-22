-- Prove2me | solution 1 for Nock.Verb.EvP_op3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:50.891871+00:00
-- url     : https://prove2.me/submissions/98f6822e-ff1f-4567-ad3f-409ae41095ff

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
theorem _root_.solution {subj tail x} : EvP subj (.cell (.atom 3) tail) x ↔
    ∃ y, EvP subj tail y ∧ x = Noun.wut y := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, hx⟩ := h
      exact ⟨y, ⟨f, hy⟩, hx.symm⟩
  · rintro ⟨y, ⟨fy, hy⟩, rfl⟩
    exact ⟨fy + 1, by simp only [evalPaper, hy, Option.map_some]⟩
end Nock.Verb
