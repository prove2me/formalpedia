-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneNegativeWeightedIntegralReflect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:36:57.651177+00:00
-- url     : https://prove2.me/submissions/c1c9fcb1-b4e2-4806-bdab-6406cbc38d8e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveWeightedJumpKernel
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLevyCompensatorReflection
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (c xi : ℝ) :
    (∫ r in Set.Iio (0 : ℝ),
      (c * |r| ^ (-2 : ℝ)) • ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand (-xi) r ∂volume) := by
  let H : ℝ → ℂ := fun r =>
    (c * |r| ^ (-2 : ℝ)) •
      ProbabilityTheory.levyCompensatedIntegrand xi r
  have hc := integral_comp_neg_Ioi (0 : ℝ) H
  rw [integral_Iic_eq_integral_Iio] at hc
  calc
    (∫ r in Set.Iio (0 : ℝ),
      (c * |r| ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
      ∫ r in Set.Ioi (0 : ℝ), H (-r) ∂volume := by
      change (∫ r in Set.Iio (0 : ℝ), H r ∂volume) =
        ∫ r in Set.Ioi (0 : ℝ), H (-r) ∂volume
      simpa only [neg_zero] using hc.symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hrpos : 0 < r := hr
      simp only [H, abs_neg, abs_of_pos hrpos]
      rw [Kyprianou.Ch01.stableAlphaOneLevyCompensatorReflection]
