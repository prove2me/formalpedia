-- Prove2me | solution 1 for MarkovProcess.dyadic_bound_normalization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:19:36.123067+00:00
-- url     : https://prove2.me/submissions/65994753-37de-4132-860d-dc8fb267b771

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_DyadicIncrementScalars
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution (p q γ : ℝ) (M : ℝ≥0) (n : ℕ) :
    (2 : ℝ≥0∞) ^ n *
        ((M : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q /
          dyadicIncrementThreshold γ n ^ p) =
      ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) := by
  have hl : (2 : ℝ≥0∞) ^ n *
        ((M : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q /
          dyadicIncrementThreshold γ n ^ p) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · simp
    apply ENNReal.div_ne_top
    · apply ENNReal.mul_ne_top
      · simp
      exact ENNReal.rpow_ne_top_of_ne_zero (by simp) (by simp)
    exact ENNReal.rpow_eq_zero_iff.not.mpr (by
      unfold dyadicIncrementThreshold
      simp)
  have hr : ((M * dyadicIncrementDecayRatio p q γ ^ n : ℝ≥0) : ℝ≥0∞) ≠ ∞ := by
    finiteness
  apply (ENNReal.toReal_eq_toReal_iff' hl hr).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_div, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_rpow,
    dyadicIncrementThreshold, dyadicIncrementDecayRatio]
  rw [← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  simp [← Real.rpow_natCast, ← Real.rpow_mul]
  rw [← Real.rpow_neg (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), div_eq_mul_inv,
    ← Real.rpow_neg (by positivity), ← Real.rpow_mul (by positivity)]
  calc
    2 ^ (n : ℝ) * ((M : ℝ) * 2 ^ (-(n : ℝ) * q) * 2 ^ (-(n : ℝ) * -(γ * p))) =
        (M : ℝ) * (2 ^ (n : ℝ) * 2 ^ (-(n : ℝ) * q) *
          2 ^ (-(n : ℝ) * -(γ * p))) := by ring_nf
    _ = (M : ℝ) * 2 ^ ((n : ℝ) + (-(n : ℝ) * q) + (-(n : ℝ) * -(γ * p))) := by
      rw [Real.rpow_add (by positivity), Real.rpow_add (by positivity)]
    _ = (M : ℝ) * 2 ^ ((1 - q + p * γ) * (n : ℝ)) := by
      congr 1
      ring_nf
