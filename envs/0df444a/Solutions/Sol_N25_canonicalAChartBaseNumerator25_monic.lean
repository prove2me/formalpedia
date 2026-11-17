-- Prove2me | solution 1 for N25.canonicalAChartBaseNumerator25_monic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:20.576797+00:00
-- url     : https://prove2.me/submissions/f4519e74-377e-4296-8793-e66a9902a604

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

/-! Regularity of the canonical multiplier in the monic A-chart presentation. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance multiplierQuotient_semiring_sc5c909 :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- The scalar numerator is monic in x. -/
theorem _root_.solution :
    ((canonicalAChartBaseX25 K)^2-canonicalAChartBaseZ25 K+1).Monic := by
  unfold canonicalAChartBaseX25 canonicalAChartBaseZ25
  monicity!

end N25
