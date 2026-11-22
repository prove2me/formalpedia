-- Prove2me | solution 1 for Nock.Verb.DenP_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:45.74897+00:00
-- url     : https://prove2.me/submissions/7afb7c44-95f9-4eb2-82e2-a59fc2212217

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_mono
public import Theorems.Thm_Nock_Verb_denP_pair
public import Theorems.Thm_Nock_evalPaper_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r x} : DenP (.node .star l r) x ↔ ∃ a b, DenP l a ∧ DenP r b ∧ EvP a b x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [denP] at h
    | succ f =>
      simp only [denP] at h
      cases hl : denP f l with
      | none => rw [hl] at h; simp at h
      | some a =>
        cases hr : denP f r with
        | none => rw [hl, hr] at h; simp at h
        | some b =>
          rw [hl, hr] at h
          exact ⟨a, b, ⟨f, hl⟩, ⟨f, hr⟩, ⟨f, h⟩⟩
  · rintro ⟨a, b, hl, hr, hev⟩
    obtain ⟨f, hl, hr⟩ := denP_pair hl hr
    obtain ⟨fe, hev⟩ := hev
    refine ⟨max f fe + 1, ?_⟩
    simp only [denP, denP_mono (show f ≤ max f fe by omega) hl, denP_mono (show f ≤ max f fe by
      omega) hr]
    exact evalPaper_mono (by omega) hev
end Nock.Verb
