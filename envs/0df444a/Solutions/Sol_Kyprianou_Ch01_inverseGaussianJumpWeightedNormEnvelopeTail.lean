-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelopeTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:17:50.026186+00:00
-- url     : https://prove2.me/submissions/08f439f2-2e6f-4834-9367-ec0bedae6792

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityPowerBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b theta x : ℝ) (hb : 0 < b) (hx : 1 < x) :
    ‖(ENNReal.ofReal
         ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
           Real.exp (-(b ^ 2 * x / 2)))).toReal •
           ((1 : ℂ) - Complex.exp
             (Complex.I * ((theta * x : ℝ) : ℂ)))‖ ≤ (|theta| + 2) * x ^ (-(3 / 2 : ℝ)) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hd : 0 ≤
      (1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)) := by positivity
  have hco : (ENNReal.ofReal
      ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)))).toReal =
      (1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)) :=
    ENNReal.toReal_ofReal hd
  have hden :=
    Kyprianou.Ch01.inverseGaussianDensityPowerBound b x hb hxpos
  have hFourier :
      ‖(1 : ℂ) -
        Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) -
        Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))‖ ≤
        ‖(1 : ℂ)‖ +
          ‖Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))‖ :=
          norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp_I_mul_ofReal]
        norm_num
  calc
    ‖(ENNReal.ofReal
         ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
           Real.exp (-(b ^ 2 * x / 2)))).toReal •
           ((1 : ℂ) - Complex.exp
             (Complex.I * ((theta * x : ℝ) : ℂ)))‖ =
        ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
          Real.exp (-(b ^ 2 * x / 2))) *
        ‖(1 : ℂ) - Complex.exp
          (Complex.I * ((theta * x : ℝ) : ℂ))‖ := by
          rw [norm_smul, hco, Real.norm_eq_abs, abs_of_nonneg hd]
    _ ≤ x ^ (-(3 / 2 : ℝ)) * 2 :=
      mul_le_mul hden hFourier (norm_nonneg _)
        (Real.rpow_nonneg hxpos.le _)
    _ ≤ (|theta| + 2) * x ^ (-(3 / 2 : ℝ)) := by
      nlinarith [abs_nonneg theta, Real.rpow_nonneg hxpos.le (-(3 / 2 : ℝ))]
