-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeTail
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:42:38.867393+00:00
-- url     : https://prove2.me/submissions/90484fab-4462-4897-85f1-cd36883dd47f

import Mathlib
open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b x : ℝ) (hb : 0 < b) (hx : 0 < x) (hx1 : 1 < x) :
    (min 1 (x ^ 2)) *
      ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2))) ≤ x ^ (-(3 / 2 : ℝ)) := by
  have hm : min 1 (x ^ 2) = 1 := min_eq_left (by nlinarith)
  rw [hm, one_mul]
  have he : Real.exp (-(b ^ 2 * x / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg b])
  have hs : Real.sqrt (x ^ 3) ≤ Real.sqrt (2 * Real.pi * x ^ 3) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three, pow_pos hx 3])
  have hs0 : 0 < Real.sqrt (x ^ 3) := Real.sqrt_pos.mpr (pow_pos hx 3)
  have hsx : Real.sqrt (x ^ 3) = x ^ (3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have h1 : 1 / Real.sqrt (2 * Real.pi * x ^ 3) ≤ x ^ (-(3/2 : ℝ)) := by
    rw [Real.rpow_neg hx.le, ← hsx, ← one_div]
    exact one_div_le_one_div_of_le hs0 hs
  have hpos : 0 ≤ 1 / Real.sqrt (2 * Real.pi * x ^ 3) := by positivity
  calc 1 / Real.sqrt (2 * Real.pi * x ^ 3) * Real.exp (-(b ^ 2 * x / 2))
      ≤ x ^ (-(3/2 : ℝ)) * 1 := by gcongr
    _ = x ^ (-(3 / 2 : ℝ)) := mul_one _
