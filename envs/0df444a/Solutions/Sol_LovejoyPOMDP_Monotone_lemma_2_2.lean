-- Prove2me | solution 1 for LovejoyPOMDP.Monotone.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:11:11.711778+00:00
-- url     : https://prove2.me/submissions/7164f3a6-24f8-4591-a703-fce074fbe941

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders

set_option autoImplicit false
open LovejoyPOMDP.Monotone

theorem solution {A : Type*} [Fintype A] [LinearOrder A] [Nonempty A] (f f' : A → ℝ)
    (h : ∀ a a' : A, a' ≤ a → f' a - f' a' ≤ f a - f a') :
    (∀ a ∈ argmaxSet f, ∃ b ∈ argmaxSet f', b ≤ a) ∧
      (∀ b ∈ argmaxSet f', ∃ a ∈ argmaxSet f, b ≤ a) := by
  obtain ⟨m, hm⟩ := Finite.exists_max f
  obtain ⟨m', hm'⟩ := Finite.exists_max f'
  constructor
  · intro a ha
    simp only [argmaxSet, Set.mem_setOf_eq] at ha
    by_cases hle : m' ≤ a
    · exact ⟨m', by simpa [argmaxSet] using hm', hle⟩
    · push_neg at hle
      refine ⟨a, ?_, le_rfl⟩
      simp only [argmaxSet, Set.mem_setOf_eq]
      intro b
      have h1 := h m' a hle.le
      have h2 := ha m'
      have h3 := hm' b
      linarith
  · intro b hb
    simp only [argmaxSet, Set.mem_setOf_eq] at hb
    by_cases hle : b ≤ m
    · exact ⟨m, by simpa [argmaxSet] using hm, hle⟩
    · push_neg at hle
      refine ⟨b, ?_, le_rfl⟩
      simp only [argmaxSet, Set.mem_setOf_eq]
      intro c
      have h1 := h b m hle.le
      have h2 := hb m
      have h3 := hm c
      linarith
