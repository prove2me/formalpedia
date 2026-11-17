-- Prove2me | solution 1 for N25.canonicalAChartBaseX25_not_mem_z
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:21.81201+00:00
-- url     : https://prove2.me/submissions/a362caf3-cbc1-41fd-b7fd-cd75614effb7

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

/-! Coordinate regularity in the monic presentation of the canonical A-chart. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance xSpecialization_semiring_s25e8c3 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

local instance zSpecialization_semiring_s25e8c3 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- x remains nonzero after setting z to zero. -/
theorem _root_.solution : canonicalAChartBaseX25 K ∉
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K)) := by
  intro h
  have hdvd := Ideal.mem_span_singleton.mp h
  let f : CanonicalAChartBase25 K →+* Polynomial K :=
    Polynomial.mapRingHom (evalRingHom (0 : K))
  have hh := map_dvd f hdvd
  have hx : (0 : Polynomial K) ∣ X := by
    simpa [f, canonicalAChartBaseX25, canonicalAChartBaseZ25] using hh
  exact X_ne_zero (zero_dvd_iff.mp hx)

end N25
