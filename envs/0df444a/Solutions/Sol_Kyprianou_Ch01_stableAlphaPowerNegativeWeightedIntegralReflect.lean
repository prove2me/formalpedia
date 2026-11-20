-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaPowerNegativeWeightedIntegralReflect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:39:36.125815+00:00
-- url     : https://prove2.me/submissions/c3529b08-4d4f-402b-8dd9-6c2c40c4f656

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLevyCompensatorReflection
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha c xi : ℝ) :
    (∫ r in Set.Iio (0 : ℝ),
      (c * |r| ^ (-alpha - 1)) • ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-alpha - 1)) •
        ProbabilityTheory.levyCompensatedIntegrand (-xi) r ∂volume) := by
  let H : ℝ → ℂ := fun r =>
    (c * |r| ^ (-alpha - 1)) •
      ProbabilityTheory.levyCompensatedIntegrand xi r
  have hc := integral_comp_neg_Ioi (0 : ℝ) H
  rw [integral_Iic_eq_integral_Iio] at hc
  calc
    (∫ r in Set.Iio (0 : ℝ),
      (c * |r| ^ (-alpha - 1)) •
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
