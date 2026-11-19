-- Prove2me | solution 1 for LevyStochCalc.norm_le_sum_abs_apply
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:52:29.45392+00:00
-- url     : https://prove2.me/submissions/39fcf5df-2530-45eb-89f2-21a4ae6ca380

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

theorem solution {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, |A (Pi.single p 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound A
    (Finset.sum_nonneg fun p _ => abs_nonneg _) fun x => ?_
  have hx : x = ∑ p : Fin n, x p • Pi.single p (1 : ℝ) := by
    ext q
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp_rw [map_smul, smul_eq_mul, Real.norm_eq_abs]
  calc
    |∑ p : Fin n, x p * A (Pi.single p 1)|
        ≤ ∑ p : Fin n, |x p * A (Pi.single p 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : Fin n, |x p| * |A (Pi.single p 1)| := by simp_rw [abs_mul]
    _ ≤ ∑ p : Fin n, ‖x‖ * |A (Pi.single p 1)| := by
        refine Finset.sum_le_sum fun p _ => ?_
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x p) (abs_nonneg _)
    _ = (∑ p : Fin n, |A (Pi.single p 1)|) * ‖x‖ := by
        rw [← Finset.mul_sum, mul_comm]
