-- Prove2me | solution 1 for Kyprianou.Ch01.gammaArrivalDensityMeasurablePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:16:26.341338+00:00
-- url     : https://prove2.me/submissions/5dd85983-1729-4063-8cbd-949994dc89eb

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Tactic.FunProp
import Definitions.Def_levy_foundations_arrivalGammaDensity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

/-- Each gamma-arrival density is measurable, by its indicator formula. -/
theorem solution (beta : ℝ) (n : ℕ) :
    Measurable (LevyFoundations.arrivalGammaDensity beta n) := by
  unfold LevyFoundations.arrivalGammaDensity
    LevyFoundations.arrivalGammaDensityReal
  apply Measurable.indicator
  · exact ENNReal.measurable_ofReal.comp (by fun_prop)
  · exact measurableSet_Ici
