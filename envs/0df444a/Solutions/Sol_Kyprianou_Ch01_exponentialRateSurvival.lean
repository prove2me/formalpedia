-- Prove2me | solution 1 for Kyprianou.Ch01.exponentialRateSurvival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:27:07.260599+00:00
-- url     : https://prove2.me/submissions/f3ee7bf8-fb85-4596-827e-367105a7a532

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Real
set_option autoImplicit false
/-! Survival of the exponential waiting-time distribution at nonnegative levels. -/
theorem solution
    (beta z : ℝ) (hbeta : 0 < beta) (hz : 0 ≤ z) :
    (ProbabilityTheory.expMeasure beta).real (Set.Ioi z) =
      Real.exp (-(beta * z)) := by
  let μ : Measure ℝ := ProbabilityTheory.expMeasure beta
  letI : IsProbabilityMeasure μ :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hbeta
  have hcompl : μ.real (Set.Ioi z) = μ.real Set.univ - μ.real (Set.Iic z) := by
    simpa only [Set.compl_Iic] using
      (measureReal_compl (μ := μ) (s := Set.Iic z) measurableSet_Iic)
  have hcdf : μ.real (Set.Iic z) = 1 - Real.exp (-(beta * z)) := by
    rw [← ProbabilityTheory.cdf_eq_real]
    simpa [μ, hz] using ProbabilityTheory.cdf_expMeasure_eq hbeta z
  change μ.real (Set.Ioi z) = _
  rw [hcompl, hcdf]
  simp [measureReal_def, measure_univ]
