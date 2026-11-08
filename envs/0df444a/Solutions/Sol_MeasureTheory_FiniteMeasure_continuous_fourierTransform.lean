-- Prove2me | solution 1 for MeasureTheory.FiniteMeasure.continuous_fourierTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:16:33.285106+00:00
-- url     : https://prove2.me/submissions/129a1b79-2ada-4d6f-abc9-5828bf4396a0

import Definitions.Def_LeanLevy_Fourier_MeasureFourier
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Trigonometric

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex

/-- The Fourier transform of a finite measure is continuous. -/
theorem solution (μ : FiniteMeasure ℝ) : Continuous (FiniteMeasure.fourierTransform μ) := by
  unfold FiniteMeasure.fourierTransform
  apply continuous_of_dominated (bound := fun _ => 1)
  · intro ξ
    exact (by fun_prop : Continuous fun x => exp (↑(ξ * x) * I)).aestronglyMeasurable
  · intro ξ
    filter_upwards with x
    simp only [norm_exp_ofReal_mul_I, le_refl]
  · exact integrable_const 1
  · filter_upwards with x
    exact by fun_prop
