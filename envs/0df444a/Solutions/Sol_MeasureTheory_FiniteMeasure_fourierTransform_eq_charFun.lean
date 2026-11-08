-- Prove2me | solution 1 for MeasureTheory.FiniteMeasure.fourierTransform_eq_charFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:47:40.625126+00:00
-- url     : https://prove2.me/submissions/457dee69-e839-48a6-a5b7-e58302b1ecab

import Definitions.Def_LeanLevy_Probability_Characteristic
import Definitions.Def_LeanLevy_Fourier_MeasureFourier
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate MeasureTheory.FiniteMeasure

/-- Source-exact equality of the finite-measure Fourier and characteristic transforms. -/
theorem solution (μ : FiniteMeasure ℝ) (ξ : ℝ) :
    fourierTransform μ ξ = charFun (μ : Measure ℝ) ξ := by
  simp only [fourierTransform, charFun_apply_real]
  congr 1
  ext x
  push_cast
  ring
