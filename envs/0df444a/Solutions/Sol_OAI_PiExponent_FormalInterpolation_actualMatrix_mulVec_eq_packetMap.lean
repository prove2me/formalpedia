-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_packetMap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:03:50.034028+00:00
-- url     : https://prove2.me/submissions/234fe541-c5bd-496b-9b3c-dae13bc4fedf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_packetMap_of_cutoff

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) (H : ℚ)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) (H : ℝ)) :
    ∃ x : Column d (H : ℝ) → ℂ,
      ∀ ρ : Row d (H : ℝ),
        (actualMatrix d (H : ℝ)).mulVecLin x ρ =
          FormalInterpolation.packetMap d (H : ℝ) P ρ := by
  apply FormalInterpolation.actualMatrix_mulVec_eq_packetMap_of_cutoff d H P
  intro i
  let w := MatrixArithmetic.logWeights (finiteDenominators d) i
  let T := MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i
  have hv : 0 < (d.v0 : ℝ) := d.v0_pos
  have ht : d.F0 * w / (d.v0 : ℝ) ≤ (T : ℝ) := by
    dsimp [T, MatrixArithmetic.truncationOrders]
    exact Nat.le_ceil _
  have hw : 0 ≤ w := by
    dsimp [w, MatrixArithmetic.logWeights]
    positivity
  have hF : 2 / (d.base.theta : ℝ) < d.F0 := d.F0_large
  have htheta : 0 < (d.base.theta : ℝ) := d.base.theta_pos
  have hprod : 2 * w / (d.base.theta : ℝ) ≤ d.F0 * w := by
    have := mul_le_mul_of_nonneg_right (le_of_lt hF) hw
    calc
      2 * w / (d.base.theta : ℝ) = (2 / (d.base.theta : ℝ)) * w := by ring
      _ ≤ d.F0 * w := this
  have ht' := mul_le_mul_of_nonneg_right ht (le_of_lt hv)
  have hscaled : d.F0 * w ≤ (T : ℝ) * (d.v0 : ℝ) := by
    calc
      d.F0 * w = (d.F0 * w / (d.v0 : ℝ)) * (d.v0 : ℝ) := by field_simp
      _ ≤ (T : ℝ) * (d.v0 : ℝ) := ht'
  have hdouble : w / (d.base.theta : ℝ) ≤ 2 * w / (d.base.theta : ℝ) := by
    apply (div_le_div_iff₀ htheta htheta).2
    nlinarith [hw]
  calc
    w / (d.base.theta : ℝ) ≤ 2 * w / (d.base.theta : ℝ) := hdouble
    _ ≤ d.F0 * w := hprod
    _ ≤ (T : ℝ) * (d.v0 : ℝ) := hscaled
