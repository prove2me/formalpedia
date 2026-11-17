-- Prove2me | solution 1 for N25.canonicalAChartTowerMultiplier25_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:28.795068+00:00
-- url     : https://prove2.me/submissions/15f1f182-9a79-44cc-9bab-52dcae22f3dd

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_isRegular_scalar_mod_root_relation
import Theorems.Thm_N25_canonicalAChartLinearRemainder25_mod_multiplier_isRegular
import Theorems.Thm_N25_canonicalAChartBaseMultiplier25_prime
import Theorems.Thm_N25_canonicalAChartQuadratic25_monic

/-! Regularity of the canonical multiplier in the monic A-chart presentation. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance multiplierQuotient_semiring_sf0a768 :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- The canonical multiplier is regular on the monic A-chart complete intersection. -/
theorem _root_.solution :
    IsRegular (Ideal.Quotient.mk _
      (AdjoinRoot.of (canonicalAChartQuadratic25 K) (canonicalAChartBaseMultiplier25 K)) :
        CanonicalAChartTowerRing25 K) := by
  exact isRegular_scalar_mod_root_relation (canonicalAChartQuadratic25 K)
    (canonicalAChartLinearRemainder25 K) (canonicalAChartBaseMultiplier25 K)
    (canonicalAChartQuadratic25_monic K) (canonicalAChartBaseMultiplier25_prime K).ne_zero
    (canonicalAChartLinearRemainder25_mod_multiplier_isRegular K)

end N25
