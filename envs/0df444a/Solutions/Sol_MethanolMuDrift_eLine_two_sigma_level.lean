-- Prove2me | solution 1 for MethanolMuDrift.eLine_two_sigma_level
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:36:11.511213+00:00
-- url     : https://prove2.me/submissions/69556021-e958-4d21-b70b-28e58e21b416

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

open MethanolMuDrift in
theorem solution :
    |muDriftEstimate eK eV eSigma| ≤ 2 * muDriftStatErr eK eSigma ∧
      |2 * muDriftStatErr eK eSigma - 1.5e-7| ≤ 0.05e-7 := by
  have hq1 : (0.023:ℝ)^2 ≤ wSum eSigma / wlsDet eK eSigma := by
    simp only [wSum, wlsDet, wSumKK, wSumK, Fin.sum_univ_three, eK, eSigma,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    norm_num
  have hq2 : wSum eSigma / wlsDet eK eSigma ≤ (0.0231:ℝ)^2 := by
    simp only [wSum, wlsDet, wSumKK, wSumK, Fin.sum_univ_three, eK, eSigma,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    norm_num
  have hb : |wlsSlope eK eV eSigma| ≤ 0.04 := by
    simp only [wlsSlope, wSum, wlsDet, wSumKK, wSumK, wSumKV, wSumV, Fin.sum_univ_three,
      eK, eV, eSigma, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [abs_le]
    constructor <;> norm_num
  have hs1 : (0.023:ℝ) ≤ wlsSlopeStdErr eK eSigma := by
    unfold wlsSlopeStdErr
    exact Real.le_sqrt_of_sq_le hq1
  have hs2 : wlsSlopeStdErr eK eSigma ≤ 0.0231 := by
    unfold wlsSlopeStdErr
    rw [Real.sqrt_le_left (by norm_num)]
    exact hq2
  have hc : (0:ℝ) < speedOfLight := by unfold speedOfLight; norm_num
  unfold muDriftEstimate muDriftStatErr
  rw [abs_div, abs_neg, abs_of_pos hc]
  constructor
  · rw [mul_div_assoc']
    apply div_le_div_of_nonneg_right _ hc.le
    linarith
  · unfold speedOfLight
    have e : 2 * (wlsSlopeStdErr eK eSigma / 299792.458) - 1.5e-7
        = (2 * wlsSlopeStdErr eK eSigma - 0.04496886870) / 299792.458 := by norm_num; ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 299792.458), div_le_iff₀ (by norm_num),
      abs_le]
    constructor <;> norm_num <;> linarith
