-- Prove2me | solution 1 for N25.canonicalAChartBaseNumerator25_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:21.210201+00:00
-- url     : https://prove2.me/submissions/3d5d32ae-cd6d-4eb4-88ae-61f82834ceee

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartBaseNumerator25_monic

/-! Regularity of the canonical multiplier in the monic A-chart presentation. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance multiplierQuotient_semiring_sf950e3 :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- The monic scalar numerator does not vanish modulo the multiplier. -/
theorem _root_.solution :
    (canonicalAChartBaseX25 K)^2-canonicalAChartBaseZ25 K+1 ∉
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K)) := by
  intro h
  have hdvd := Ideal.mem_span_singleton.mp h
  have hu := (canonicalAChartBaseNumerator25_monic K).isUnit_leadingCoeff_of_dvd hdvd
  have hlc : (canonicalAChartBaseMultiplier25 K).leadingCoeff = (X : Polynomial K)+1 := by
    have he : canonicalAChartBaseMultiplier25 K = C (X+1)*X+C X := by
      unfold canonicalAChartBaseMultiplier25 canonicalAChartBaseX25 canonicalAChartBaseZ25
      simp only [map_add, map_one]
      ring
    rw [he]
    exact leadingCoeff_linear (monic_X_add_C 1).ne_zero
  rw [hlc] at hu
  exact not_isUnit_X_add_C (1 : K) hu

end N25
