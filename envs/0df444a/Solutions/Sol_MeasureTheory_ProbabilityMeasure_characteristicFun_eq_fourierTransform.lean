-- Prove2me | solution 1 for MeasureTheory.ProbabilityMeasure.characteristicFun_eq_fourierTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:06:44.713529+00:00
-- url     : https://prove2.me/submissions/d1d694f3-be73-4b5e-ba93-8fca684dd39f

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Definitions.Def_LeanLevy_Probability_Characteristic
import Theorems.Thm_MeasureTheory_FiniteMeasure_fourierTransform_eq_charFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate MeasureTheory.ProbabilityMeasure

/-- Source-exact characteristic-function and finite Fourier-transform bridge. -/
theorem solution (μ : ProbabilityMeasure ℝ) (ξ : ℝ) :
    characteristicFun μ ξ = FiniteMeasure.fourierTransform μ.toFiniteMeasure ξ := by
  simp [characteristicFun, FiniteMeasure.fourierTransform_eq_charFun]
