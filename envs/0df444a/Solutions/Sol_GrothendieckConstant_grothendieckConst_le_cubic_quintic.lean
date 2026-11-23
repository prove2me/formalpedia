-- Prove2me | solution 1 for GrothendieckConstant.grothendieckConst_le_cubic_quintic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T15:49:59.762503+00:00
-- url     : https://prove2.me/submissions/642af0cb-1bb9-49c5-b115-570b132bc2d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_exists_limitingScheme_cqCorr
import Theorems.Thm_GrothendieckLB_Supplement_limitingScheme_bound_of_coefficient_gap
import Theorems.Thm_GrothendieckLB_Supplement_cq_coefficient_estimates_at_251
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential

open GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement

set_option maxHeartbeats 800000 in
private theorem compare_cubic_quintic_constant :
    Real.pi / (2 * 0.881545409) ≤
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  have hsqrt : Real.sqrt 2 ≤ 1.414213563 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hexp : (2.414213563 : ℝ) ≤ Real.exp 0.8813736 := by
    calc
      _ ≤ ∑ j ∈ Finset.range 11, (0.8813736 : ℝ) ^ j / j.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) 11
  have hlog : Real.log (1 + Real.sqrt 2) ≤ 0.8813736 := by
    apply (Real.log_le_iff_le_exp (by positivity)).2
    linarith only [hsqrt, hexp]
  have hlog_pos : 0 < Real.log (1 + Real.sqrt 2) := by
    apply Real.log_pos
    have h := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hdiv : Real.pi / (2 * 0.8813736) ≤ Real.pi / (2 * Real.log (1 + Real.sqrt 2)) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith only [hlog])
  calc
    Real.pi / (2 * 0.881545409) ≤ Real.pi / (2 * 0.8813736) - 3.47 * 10 ^ (-4 : ℤ) := by
      norm_num [div_eq_mul_inv] <;> linarith only [Real.pi_gt_d2]
    _ ≤ _ := sub_le_sub_right hdiv _

theorem solution :
    grothendieckConst ≤
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  let a (j : ℕ) := |taylorCoeff (2 * j + 3) H|
  obtain ⟨S, hS⟩ := exists_limitingScheme_cqCorr 0.136419125 0.34101124 0.05276111
  change S.corr = H at hS
  obtain ⟨hlinear, hhead, htail_sum, htail⟩ := cq_coefficient_estimates_at_251
  change 0.881573822049 ≤ taylorCoeff 1 H at hlinear
  change (∑ j ∈ Finset.range 125, a j) ≤ 0.000011328860 at hhead
  have hshift (j : ℕ) : a (j + 125) = |taylorCoeff (2 * j + 253) H| := by
    dsimp only [a]
    rw [show 2 * (j + 125) + 3 = 2 * j + 253 by omega]
  have hsum : Summable a := by
    apply (summable_nat_add_iff (f := a) 125).1
    simpa only [hshift] using htail_sum
  have hsqrt : (14.443 / 0.000004575864 : ℝ) ≤ Real.sqrt (10 * (251 : ℝ) ^ 5) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have htail_num : 14.443 / Real.sqrt (10 * (251 : ℝ) ^ 5) ≤ 0.000004575864 := by
    apply (div_le_iff₀ (by positivity)).2
    simpa only [mul_comm] using
      (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.000004575864)).mp hsqrt
  have hmass : (∑' j, a j) ≤ 0.000015904724 := by
    rw [← hsum.sum_add_tsum_nat_add 125]
    have htail' : (∑' j : ℕ, a (j + 125)) ≤ 0.000004575864 := by
      simpa only [hshift] using htail.trans htail_num
    linarith only [hhead, htail']
  have hgap : 0.881545409 + (∑' j, a j) < taylorCoeff 1 H := by
    linarith only [hmass, hlinear]
  refine le_trans ?_ compare_cubic_quintic_constant
  apply limitingScheme_bound_of_coefficient_gap S 0.881545409 (by norm_num)
  · rw [hS]
    exact hsum
  · rw [hS]
    exact hgap
