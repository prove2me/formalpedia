-- Prove2me | solution 1 for N25.canonicalAChartBaseMultiplierQuotient25_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:20.026256+00:00
-- url     : https://prove2.me/submissions/e0fb8385-c417-472f-823e-701f5b06cf1d

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartBaseMultiplier25_prime

/-! Regularity of the canonical multiplier in the monic A-chart presentation. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance multiplierQuotient_semiring_s2705ca :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- Its specialization quotient is a domain. -/
theorem _root_.solution :
    IsDomain (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) := by
  apply (Ideal.Quotient.isDomain_iff_prime
    (Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K)))).mpr
  exact (Ideal.span_singleton_prime (canonicalAChartBaseMultiplier25_prime K).ne_zero).mpr
    (canonicalAChartBaseMultiplier25_prime K)

end N25
