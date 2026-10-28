-- Prove2me | solution 2 for MeasureTheory.le_measure_ge_of_lintegral_sq_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:09:48.921895+00:00
-- url     : https://prove2.me/submissions/3deb2dcc-0194-476e-ab90-75da169c76a2

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_MeasureTheory_lintegral_le_rpow_lintegral_sq
import Theorems.Thm_MeasureTheory_lintegral_sq_mul_measure_ge_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal NNReal
open MeasureTheory
variable {Omega : Type*} [MeasurableSpace Omega]

theorem solution (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) (hsq : ∫⁻ omega, Z omega ^ 2 ∂mu ≠ ⊤)
    (rho : ℝ≥0) :
    ((1 : ℝ≥0∞) - rho) ^ 2 * (∫⁻ omega, Z omega ∂mu) ^ 2 / (∫⁻ omega, Z omega ^ 2 ∂mu) ≤
      mu {omega | (rho : ℝ≥0∞) * ∫⁻ omega, Z omega ∂mu ≤ Z omega} := by
  have hfin : ∫⁻ omega, Z omega ∂mu ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_le_rpow_lintegral_sq mu hZ.aemeasurable)
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hsq
  exact ENNReal.div_le_of_le_mul
    ((lintegral_sq_mul_measure_ge_le mu hZ hfin rho).trans_eq (mul_comm _ _))
