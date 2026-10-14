-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-12T19:59:57.294505+00:00
-- url     : https://prove2.me/submissions/f50c05db-295a-4dee-8be0-fe8d73dc8675
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_eventual_scaled_packets
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncated_matrix_of_packets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

private theorem admissible_logWeight_pos {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
  have h : MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) := by
    simp only [MatrixArithmetic.logWeights, finiteDenominators, d.x_log]
  rw [h]
  exact zero_lt_one.trans_le (d.x_one_le _)

private theorem admissible_truncation_bound {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
        (d.v0 : ℝ) := by
  have hw := admissible_logWeight_pos d i
  have hF : 1 / (d.base.theta : ℝ) < d.F0 :=
    (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) d.base.theta_pos).trans d.F0_large
  have hceil := Nat.le_ceil
    (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i / (d.v0 : ℝ))
  calc
    _ = (1 / (d.base.theta : ℝ)) *
        MatrixArithmetic.logWeights (finiteDenominators d) i := by ring
    _ ≤ d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i :=
      mul_le_mul_of_nonneg_right hF.le hw.le
    _ ≤ _ := (div_le_iff₀ d.v0_pos).mp hceil

theorem solution : GlobalInterpolationStatement := by
  intro nu hnu d L
  obtain ⟨R, hR, N, hN⟩ :=
    OAI.PiExponent.AdmissibleFormalInterpolation.eventual_scaled_packets nu hnu d
  let n : ℕ := max N (Nat.ceil (L / (R : ℝ)))
  have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hL : L ≤ (n : ℝ) * (R : ℝ) := by
    apply (div_le_iff₀ hRreal).mp
    exact (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right N (Nat.ceil (L / (R : ℝ)))))
  refine ⟨(n : ℝ) * (R : ℝ), hL, ?_⟩
  exact OAI.PiExponent.AdmissibleFormalInterpolation.truncated_matrix_of_packets
    d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) _
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    d.w0_pos d.v0_pos d.base.theta_pos (admissible_logWeight_pos d)
    (admissible_truncation_bound d) (hN n (le_max_left _ _))
