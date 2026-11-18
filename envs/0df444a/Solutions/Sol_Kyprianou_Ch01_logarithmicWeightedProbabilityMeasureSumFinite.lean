-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicWeightedProbabilityMeasureSumFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:11:32.718787+00:00
-- url     : https://prove2.me/submissions/43bfe1f4-b77d-4936-880d-074a12c9a26c

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_realLogSeriesMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false
/-! Summable positive logarithmic weights make a finite intensity on any probability clusters. -/
theorem solution
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ν : ℕ → Measure ℝ)
    (hν : ∀ n : ℕ, IsProbabilityMeasure (ν n)) :
    (Measure.sum fun n : ℕ =>
      (ENNReal.ofReal (q ^ (n + 1) / (n + 1 : ℝ))) • ν n)
      Set.univ < ⊤ := by
  have hs := (Kyprianou.Ch01.realLogSeriesMass q hq0 hq1).summable
  have htotal (n : ℕ) : ν n Set.univ = 1 := by
    letI : IsProbabilityMeasure (ν n) := hν n
    exact measure_univ
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, htotal, smul_eq_mul, mul_one]
  exact hs.tsum_ofReal_lt_top
