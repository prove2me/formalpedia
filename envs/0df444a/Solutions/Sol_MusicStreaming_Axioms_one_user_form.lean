-- Prove2me | solution 1 for MusicStreaming.Axioms.one_user_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:23:15.021889+00:00
-- url     : https://prove2.me/submissions/0f6c7663-e969-4e2d-9211-9a45097b2ab4

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

set_option autoImplicit false
open MusicStreaming.Axioms

theorem solution {n : ℕ} (I : Index n) (hH : Homogeneity I) :
    ∀ (j : ℕ) (x : Fin n → ℕ), x ≠ 0 → ∀ i : Fin n,
      I (Finsupp.single j x) i =
        (∑ i', I (Finsupp.single j x) i') / (∑ i', (x i' : ℝ)) * x i := by
  intro j x hx i
  set t : Problem n := Finsupp.single j x with ht
  have hsupp : t.support = {j} := Finsupp.support_single_ne_zero j hx
  have hcol : ∀ j' ∈ t.support, t j' = x := by
    intro j' hj'
    rw [hsupp] at hj'
    have : j' = j := by simpa using hj'
    subst this
    simp [t]
  have hT : 0 < ∑ i', (x i' : ℝ) := by
    obtain ⟨i0, hi0⟩ : ∃ i0, x i0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
      ⟨i0, Finset.mem_univ _, by exact_mod_cast Nat.pos_of_ne_zero hi0⟩
  have key : ∀ i i' : Fin n, I t i * x i' = I t i' * x i := by
    intro i i'
    by_cases h : x i' = 0
    · have h1 := hH t i' i 0 le_rfl (by
        intro j' hj'
        rw [hcol j' hj']
        simp [h])
      have : I t i' = 0 := by simpa using h1
      simp [h, this]
    · have hpos : (x i' : ℝ) ≠ 0 := by exact_mod_cast h
      have h1 := hH t i i' ((x i : ℝ) / x i') (by positivity) (by
        intro j' hj'
        rw [hcol j' hj']
        field_simp)
      rw [h1]
      field_simp
  rw [div_mul_eq_mul_div, eq_div_iff hT.ne', Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i' _ => key i i'
