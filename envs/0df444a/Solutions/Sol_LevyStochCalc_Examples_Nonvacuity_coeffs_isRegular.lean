-- Prove2me | solution 1 for LevyStochCalc.Examples.Nonvacuity.coeffs_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T02:48:33.493664+00:00
-- url     : https://prove2.me/submissions/5c5a2449-0102-4f94-86d9-45014b576c6b

import Definitions.Def_NonvacuityItoLevy_F000

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open LevyStochCalc.Examples.Nonvacuity

theorem solution : coeffs.IsRegular jumpIntensity := by
  refine ⟨measurable_uncurry_mu, measurable_uncurry_sigma, measurable_gamma, ?_, ?_, ?_⟩
  · intro T hT
    simp [coeffs]
  · intro T hT
    simp [coeffs, Fin.sum_univ_one, ENNReal.ofReal_lt_top]
  · intro T hT
    simp [coeffs, jumpIntensity, Fin.sum_univ_one, ENNReal.ofReal_lt_top]
