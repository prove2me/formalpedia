-- Prove2me | solution 2 for GrothendieckConstant.grothendieckConst_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:48:03.6616+00:00
-- url     : https://prove2.me/submissions/568eb45e-3351-43a7-a95f-72214d341b17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckConstant_affine_constraint_transfer
import Theorems.Thm_GrothendieckConstant_krivine_scheme_affine_constraint
import Theorems.Thm_GrothendieckLB_Supplement_theorem_4_2

open GrothendieckConstant

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
  · obtain ⟨_, _, hradius, _, _⟩ := GrothendieckLB.Supplement.theorem_4_2
    exact hradius.trans compare_cubic_quintic_radius
