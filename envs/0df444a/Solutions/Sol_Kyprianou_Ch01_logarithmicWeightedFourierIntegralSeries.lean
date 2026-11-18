-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicWeightedFourierIntegralSeries
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:15:56.709325+00:00
-- url     : https://prove2.me/submissions/fc972c5c-f693-4ade-980a-adbf2efc2a70

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicWeightedProbabilityMeasureSumFinite
import Theorems.Thm_Kyprianou_Ch01_finiteLevyCompensatedFourierIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex
open scoped ENNReal BigOperators
set_option autoImplicit false
/-! Bochner integral against the finite logarithmic measure sum is its weighted series. -/
theorem solution
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ν : ℕ → Measure ℝ) (hν : ∀ n : ℕ, IsProbabilityMeasure (ν n))
    (xi : ℝ) :
    (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1)
        ∂(Measure.sum fun n : ℕ =>
          (ENNReal.ofReal (q ^ (n + 1) / (n + 1 : ℝ))) • ν n)) =
    ∑' n : ℕ,
      ((q ^ (n + 1) / (n + 1 : ℝ) : ℝ) : ℂ) *
      (∫ x : ℝ,
        (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂ν n) := by
  let M : Measure ℝ := Measure.sum fun n : ℕ =>
      (ENNReal.ofReal (q ^ (n + 1) / (n + 1 : ℝ))) • ν n
  have hmass : M Set.univ < ⊤ :=
    Kyprianou.Ch01.logarithmicWeightedProbabilityMeasureSumFinite q hq0 hq1 ν hν
  letI : IsFiniteMeasure M := ⟨hmass⟩
  have hint := Kyprianou.Ch01.finiteLevyCompensatedFourierIntegrable M xi
  change (∫ x : ℝ,
    (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂M) = _
  rw [integral_sum_measure hint]
  apply tsum_congr
  intro n
  rw [integral_smul_measure]
  have hw : 0 ≤ q ^ (n + 1) / (n + 1 : ℝ) := by
    positivity
  rw [ENNReal.toReal_ofReal hw]
  simp only [Complex.real_smul]
