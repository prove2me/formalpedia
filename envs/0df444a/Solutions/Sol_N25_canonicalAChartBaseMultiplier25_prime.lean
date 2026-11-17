-- Prove2me | solution 1 for N25.canonicalAChartBaseMultiplier25_prime
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:56.328016+00:00
-- url     : https://prove2.me/submissions/52165c78-a992-43d8-a8cf-db67c728eb43

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartBaseMultiplier25_irreducible

/-! Regularity of the canonical multiplier in the monic A-chart presentation. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance multiplierQuotient_semiring_s8996ee :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- The multiplier is prime in the polynomial coefficient ring. -/
theorem _root_.solution :
    Prime (canonicalAChartBaseMultiplier25 K) :=
  irreducible_iff_prime.mp (canonicalAChartBaseMultiplier25_irreducible K)

end N25
