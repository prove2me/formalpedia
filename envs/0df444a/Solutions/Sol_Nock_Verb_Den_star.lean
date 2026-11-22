-- Prove2me | solution 1 for Nock.Verb.Den_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:48.75111+00:00
-- url     : https://prove2.me/submissions/e49c3094-a24d-400f-a87e-0f5f076fc62b

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_mono
public import Theorems.Thm_Nock_Verb_den_pair
public import Theorems.Thm_Nock_evalN_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r x} : Den (.node .star l r) x ↔ ∃ a b, Den l a ∧ Den r b ∧ Ev a b x := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [den] at h
    | succ f =>
      simp only [den] at h
      cases hl : den f l with
      | none => rw [hl] at h; simp at h
      | some a =>
        cases hr : den f r with
        | none => rw [hl, hr] at h; simp at h
        | some b =>
          rw [hl, hr] at h
          exact ⟨a, b, ⟨f, hl⟩, ⟨f, hr⟩, ⟨f, h⟩⟩
  · rintro ⟨a, b, hl, hr, hev⟩
    obtain ⟨f, hl, hr⟩ := den_pair hl hr
    obtain ⟨fe, hev⟩ := hev
    refine ⟨max f fe + 1, ?_⟩
    simp only [den, den_mono (show f ≤ max f fe by omega) hl, den_mono (show f ≤ max f fe by omega)
      hr]
    exact evalN_mono (by omega) hev
end Nock.Verb
