-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_scaled_image
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:47:20.045161+00:00
-- url     : https://prove2.me/submissions/32e6af5b-780a-4a94-9a68-8ffd61a2bf72

import Mathlib

open scoped BigOperators
theorem solution (k : ℕ) (U : ℝ) (hU : 0 < U) :
    (fun x : Fin k → ℝ => U • x) ''
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1} =
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ U} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨h0, hs⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hU.le (h0 i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      nlinarith
  · rintro ⟨h0, hs⟩
    refine ⟨U⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hU.le) (h0 i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [inv_mul_le_iff₀ hU]; linarith
    · rw [smul_smul, mul_inv_cancel₀ hU.ne', one_smul]
