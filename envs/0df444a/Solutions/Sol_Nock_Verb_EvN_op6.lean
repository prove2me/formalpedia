-- Prove2me | solution 1 for Nock.Verb.EvN_op6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:31.281086+00:00
-- url     : https://prove2.me/submissions/e2f02775-9496-4357-be65-47e604535bef

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_ev2

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 6) tail) x ↔
    ∃ b c d cv, tail = .cell b (.cell c d) ∧ Ev subj b cv ∧
      ((cv = .atom 0 ∧ Ev subj c x) ∨ (cv = .atom 1 ∧ Ev subj d x)) := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f =>
      simp only [evalN] at h
      cases tail with
      | atom => simp at h
      | cell b rest =>
        cases rest with
        | atom => simp at h
        | cell c d =>
          simp only at h
          cases hb : evalN f subj b with
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
    · obtain ⟨f, hcv, hc⟩ := ev2 hcv hc
      refine ⟨f + 1, ?_⟩; rw [evalN, hcv]; exact hc
    · obtain ⟨f, hcv, hd⟩ := ev2 hcv hd
      refine ⟨f + 1, ?_⟩; rw [evalN, hcv]; exact hd
end Nock.Verb
