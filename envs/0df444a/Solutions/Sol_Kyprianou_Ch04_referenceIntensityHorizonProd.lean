-- Prove2me | solution 1 for Kyprianou.Ch04.referenceIntensityHorizonProd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:44:30.012947+00:00
-- url     : https://prove2.me/submissions/50e320c3-be1b-48b1-a2bd-b5fbbb37d62e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The restricted reference intensity is the product of the time and mark measures. -/
theorem solution (nu : Measure ℝ) [SigmaFinite nu] (t : NNReal) :
    (referenceIntensity nu).restrict (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)) =
      (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod nu := by
  unfold referenceIntensity
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_restrict_of_subset (fun x hx => hx.1)]
