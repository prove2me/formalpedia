-- Prove2me | solution 1 for Kyprianou.Ch04.referenceIntensityClosedWindowProductV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:29:48.148804+00:00
-- url     : https://prove2.me/submissions/118d8f1c-7316-4abc-82c6-46e09fcf0a9e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The physical reference intensity on a nonnegative closed time window
is precisely the restricted time volume times the mark measure. -/
theorem solution (ν : Measure ℝ) [SigmaFinite ν] (T : NNReal) (B : Set ℝ)
    (hB : MeasurableSet B) :
    (referenceIntensity ν).restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ B) =
    (volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod (ν.restrict B) := by
  rw [referenceIntensity,← Measure.prod_restrict,
    Measure.restrict_restrict measurableSet_Icc]
  congr 2
  exact inter_eq_left.mpr fun t ht => ht.1
