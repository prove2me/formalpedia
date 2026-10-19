-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_dilation_image
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:44:54.538124+00:00
-- url     : https://prove2.me/submissions/afdcf298-f6a6-441d-9b16-f4088a806e56

import Mathlib

open scoped BigOperators
theorem solution (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ a} =
      Set.image (fun x : Fin m → ℝ => a • x)
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h0, hs⟩
    rcases eq_or_lt_of_le ha with rfl | hpos
    · refine ⟨0, ⟨fun _ => le_rfl, by simp⟩, ?_⟩
      have hx0 : ∀ i, x i = 0 := by
        intro i
        have := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
        linarith [h0 i]
      funext i; simp [hx0 i]
    · refine ⟨a⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr ha) (h0 i)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ hpos]; linarith
      · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  · rintro ⟨y, ⟨h0, hs⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg ha (h0 i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      nlinarith
