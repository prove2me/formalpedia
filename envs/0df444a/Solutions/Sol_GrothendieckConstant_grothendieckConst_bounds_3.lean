-- Prove2me | solution 3 for GrothendieckConstant.grothendieckConst_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:34:35.954634+00:00
-- url     : https://prove2.me/submissions/1b69767a-0e4b-4d0c-9f6f-fc5351676041
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckConstant_affine_constraint_transfer
import Theorems.Thm_GrothendieckConstant_krivine_scheme_affine_constraint
import Theorems.Thm_GrothendieckLB_Supplement_exists_limitingScheme_cqCorr
import Theorems.Thm_GrothendieckLB_Supplement_cq_coefficient_estimates_at_251
import Theorems.Thm_GrothendieckLB_Supplement_limitingScheme_bound_of_coefficient_gap

open GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement

private theorem compare_cubic_quintic_radius :
    Real.pi / (2 * (0.881545409 : ℝ)) ≤
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  have hsqrt : Real.sqrt 2 ≤ (1.41421357 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hlog : Real.log (1 + Real.sqrt 2) ≤ 0.8813736 := by
    apply (Real.log_le_iff_le_exp (show 0 < 1 + Real.sqrt 2 by positivity)).2
    calc
      1 + Real.sqrt 2 ≤ 1 + 1.41421357 := by linarith only [hsqrt]
      _ ≤ ∑ j ∈ Finset.range 11, (0.8813736 : ℝ) ^ j / (j.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial_succ]
      _ ≤ Real.exp 0.8813736 := Real.sum_le_exp_of_nonneg (by norm_num) 11
  have hpos : 0 < Real.log (1 + Real.sqrt 2) :=
    Real.log_pos (lt_add_of_pos_right _ (by positivity))
  apply le_sub_iff_add_le.mpr
  calc
    Real.pi / (2 * (0.881545409 : ℝ)) + 3.47 * 10 ^ (-4 : ℤ) ≤
        Real.pi / (2 * (0.8813736 : ℝ)) := by
      norm_num <;> linarith only [Real.pi_gt_d2]
    _ ≤ Real.pi / (2 * Real.log (1 + Real.sqrt 2)) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (mul_pos (by norm_num) hpos)
        (mul_le_mul_of_nonneg_left hlog (by norm_num))

private theorem scheme_bound : grothendieckConst ≤ Real.pi/(2*0.881545409) := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  let a (j : ℕ) := |taylorCoeff (2*j+3) H|
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
  have hsumS : Summable (fun j : ℕ => |taylorCoeff (2*j+3) S.corr|) := by
    rw [hS]
    exact hsum
  have hgapS : 0.881545409 + (∑' j : ℕ, |taylorCoeff (2*j+3) S.corr|) <
      taylorCoeff 1 S.corr := by
    rw [hS]
    exact hgap
  exact limitingScheme_bound_of_coefficient_gap S 0.881545409 (by norm_num) hsumS hgapS

theorem solution :
    6 * Real.pi / 11 ≤ grothendieckConst ∧
      grothendieckConst ≤
        Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  constructor
  · calc
      6 * Real.pi / 11 = Real.pi * (1 + 1) / (2 * (1 + 5 / 6)) := by ring
      _ ≤ grothendieckConst := by
        apply affine_constraint_transfer 1 (by norm_num)
        intro k S
        calc
          (1 + 1) * coeffLinear S - (1 + 5 / 6) =
              2 * coeffLinear S - 11 / 6 := by ring
          _ ≤ coeffCubic S := krivine_scheme_affine_constraint k S
  · exact scheme_bound.trans compare_cubic_quintic_radius
