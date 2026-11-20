-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelopeNearZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:22:16.380726+00:00
-- url     : https://prove2.me/submissions/81203a2e-4ee7-453d-be21-e46e52254320

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityPowerBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b theta x : ℝ) (hb : 0 < b) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖(ENNReal.ofReal
         ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
           Real.exp (-(b ^ 2 * x / 2)))).toReal •
           ((1 : ℂ) - Complex.exp
             (Complex.I * ((theta * x : ℝ) : ℂ)))‖ ≤ (|theta| + 2) * x ^ (-(1 / 2 : ℝ)) := by
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
    Kyprianou.Ch01.inverseGaussianDensityPowerBound b x hb hx
  have hfourier :
      ‖(1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))‖ ≤
        |theta * x| := by
    calc
      ‖(1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))‖ =
          ‖Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ)) -
            (1 : ℂ)‖ := norm_sub_rev _ _
      _ ≤ |theta * x| := by
        simpa using
          (Real.norm_exp_I_mul_ofReal_sub_one_le (x := theta * x))
  have hxp : x ^ (-(3 / 2 : ℝ)) * x =
      x ^ (-(1 / 2 : ℝ)) := by
    calc
      x ^ (-(3 / 2 : ℝ)) * x =
        x ^ (-(3 / 2 : ℝ)) * x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = x ^ (-(3 / 2 : ℝ) + 1) :=
        (Real.rpow_add hx _ _).symm
      _ = x ^ (-(1 / 2 : ℝ)) := by congr 1; ring
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
    _ ≤ x ^ (-(3 / 2 : ℝ)) * |theta * x| :=
      mul_le_mul hden hfourier (norm_nonneg _)
        (Real.rpow_nonneg hx.le _)
    _ = |theta| * (x ^ (-(3 / 2 : ℝ)) * x) := by
      rw [abs_mul, abs_of_pos hx]
      ring
    _ = |theta| * x ^ (-(1 / 2 : ℝ)) := by rw [hxp]
    _ ≤ (|theta| + 2) * x ^ (-(1 / 2 : ℝ)) := by
      gcongr
      norm_num
