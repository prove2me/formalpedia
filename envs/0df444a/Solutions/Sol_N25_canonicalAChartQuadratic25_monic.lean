-- Prove2me | solution 1 for N25.canonicalAChartQuadratic25_monic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:59.294594+00:00
-- url     : https://prove2.me/submissions/df1bd70d-2073-4c9e-ac89-b99d69f3a8e2

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

/-! Regularity of the canonical multiplier in the monic A-chart presentation. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance multiplierQuotient_semiring_sc34f35 :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- The A-chart quadric is monic in its separated y coordinate. -/
theorem _root_.solution : (canonicalAChartQuadratic25 K).Monic := by
  let x := canonicalAChartBaseX25 K
  let z := canonicalAChartBaseZ25 K
  have h : degree (C (2*z-x)*X+C (z^2-2*x*z+x-z)) < 2 := by
    compute_degree; norm_num
  convert monic_X_pow_add h using 1
  unfold canonicalAChartQuadratic25
  dsimp [x, z]
  ring

end N25
