-- Prove2me | solution 1 for LevyStochCalc.norm_le_sum_abs_apply_u2082__p2m_487d91410cc5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:55:32.813693+00:00
-- url     : https://prove2.me/submissions/01b106f1-a65c-4b06-9442-cb4bca4f64e7

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwoVector_F000

open ContinuousLinearMap

theorem solution {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by
  have h1 : ∀ (B : (Fin n → ℝ) →L[ℝ] ℝ), ‖B‖ ≤ ∑ q, |B (Pi.single q 1)| := by
    intro B
    refine ContinuousLinearMap.opNorm_le_bound B
      (Finset.sum_nonneg fun q _ => abs_nonneg _) fun y => ?_
    have hy : y = ∑ q : Fin n, y q • Pi.single q (1 : ℝ) := by
      ext r; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul, Real.norm_eq_abs]
    calc |∑ q : Fin n, y q * B (Pi.single q 1)|
        ≤ ∑ q : Fin n, |y q * B (Pi.single q 1)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q : Fin n, |y q| * |B (Pi.single q 1)| := by simp_rw [abs_mul]
      _ ≤ ∑ q : Fin n, ‖y‖ * |B (Pi.single q 1)| :=
          Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (norm_le_pi_norm y q) (abs_nonneg _)
      _ = (∑ q : Fin n, |B (Pi.single q 1)|) * ‖y‖ := by rw [← Finset.mul_sum, mul_comm]
  refine ContinuousLinearMap.opNorm_le_bound A
    (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _) fun x => ?_
  have hx : x = ∑ p : Fin n, x p • Pi.single p (1 : ℝ) := by
    ext r; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp_rw [map_smul]
  calc ‖∑ p : Fin n, x p • A (Pi.single p 1)‖
      ≤ ∑ p : Fin n, ‖x p • A (Pi.single p 1)‖ := norm_sum_le _ _
    _ = ∑ p : Fin n, |x p| * ‖A (Pi.single p 1)‖ := by simp_rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ p : Fin n, ‖x‖ * (∑ q, |A (Pi.single p 1) (Pi.single q 1)|) := by
        refine Finset.sum_le_sum fun p _ => ?_
        exact mul_le_mul (norm_le_pi_norm x p) (h1 (A (Pi.single p 1))) (norm_nonneg _) (norm_nonneg _)
    _ = (∑ p, ∑ q, |A (Pi.single p 1) (Pi.single q 1)|) * ‖x‖ := by
        rw [← Finset.mul_sum, mul_comm]
