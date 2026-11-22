-- Prove2me | solution 1 for Nock.Verb.EvP_op6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:46.947413+00:00
-- url     : https://prove2.me/submissions/339907f3-24bc-4dad-a19b-a774a534f972

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_ev2P

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj tail x} : EvP subj (.cell (.atom 6) tail) x ↔
    ∃ b c d cv, tail = .cell b (.cell c d) ∧ EvP subj b cv ∧
      ((cv = .atom 0 ∧ EvP subj c x) ∨ (cv = .atom 1 ∧ EvP subj d x)) := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalPaper] at h
    | succ f =>
      simp only [evalPaper] at h
      cases tail with
      | atom => simp at h
      | cell b rest =>
        cases rest with
        | atom => simp at h
        | cell c d =>
          simp only at h
          cases hb : evalPaper f subj b with
          | none => rw [hb] at h; simp at h
          | some bv =>
            cases bv with
            | cell => rw [hb] at h; simp at h
            | atom k =>
              rw [hb] at h
              cases k with
              | zero => exact ⟨b, c, d, .atom 0, rfl, ⟨f, hb⟩, Or.inl ⟨rfl, ⟨f, h⟩⟩⟩
              | succ k =>
                cases k with
                | zero => exact ⟨b, c, d, .atom 1, rfl, ⟨f, hb⟩, Or.inr ⟨rfl, ⟨f, h⟩⟩⟩
                | succ k => simp at h
  · rintro ⟨b, c, d, cv, rfl, hcv, hor⟩
    rcases hor with ⟨rfl, hc⟩ | ⟨rfl, hd⟩
    · obtain ⟨f, hcv, hc⟩ := ev2P hcv hc
      refine ⟨f + 1, ?_⟩; rw [evalPaper, hcv]; exact hc
    · obtain ⟨f, hcv, hd⟩ := ev2P hcv hd
      refine ⟨f + 1, ?_⟩; rw [evalPaper, hcv]; exact hd
end Nock.Verb
