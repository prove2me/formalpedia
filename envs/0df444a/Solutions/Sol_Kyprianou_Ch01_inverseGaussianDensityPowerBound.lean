-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianDensityPowerBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:21:05.721765+00:00
-- url     : https://prove2.me/submissions/e8e3fd23-f2d7-40da-b58f-7e78036cf175

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Inverse Gaussian jump density is bounded by x to the minus three halves. -/
theorem solution (b x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    (1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)) ≤ x ^ (-(3 / 2 : ℝ)) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
    have hp := Real.one_le_pi_div_two
    nlinarith
  have hx3 : 0 < x ^ 3 := pow_pos hx _
  have harg : x ^ 3 ≤ 2 * Real.pi * x ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hx3.le]
  have hroot : Real.sqrt (x ^ 3) ≤
      Real.sqrt (2 * Real.pi * x ^ 3) :=
    Real.sqrt_le_sqrt harg
  have hrootPos : 0 < Real.sqrt (x ^ 3) :=
    Real.sqrt_pos.2 hx3
  have hrecip : 1 / Real.sqrt (2 * Real.pi * x ^ 3) ≤
      1 / Real.sqrt (x ^ 3) :=
    one_div_le_one_div_of_le hrootPos hroot
  have hrootEq : Real.sqrt (x ^ 3) = x ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3,
      ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hpower : 1 / Real.sqrt (x ^ 3) =
      x ^ (-(3 / 2 : ℝ)) := by
    rw [hrootEq, Real.rpow_neg hx.le]
    simp only [one_div]
  have hexp : Real.exp (-(b ^ 2 * x / 2)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by
      have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
      nlinarith [mul_nonneg hb2 hx.le])
  calc
    (1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)) ≤
        (1 / Real.sqrt (2 * Real.pi * x ^ 3)) * 1 :=
      mul_le_mul_of_nonneg_left hexp
        (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = 1 / Real.sqrt (2 * Real.pi * x ^ 3) := by ring
    _ ≤ 1 / Real.sqrt (x ^ 3) := hrecip
    _ = x ^ (-(3 / 2 : ℝ)) := hpower
