-- Prove2me | solution 1 for N25.canonicalAChartTowerX25_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:29.54519+00:00
-- url     : https://prove2.me/submissions/d49e2302-e0bb-41c5-863e-f2d54d590977

import Mathlib
import Theorems.Thm_N25_canonicalAChartQuadratic25_monic
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_isRegular_scalar_mod_root_relation
import Theorems.Thm_N25_canonicalAChartLinearRemainder25_mod_x_isRegular

/-! Coordinate regularity in the monic presentation of the canonical A-chart. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance xSpecialization_semiring_sda1b5f : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- x is regular in the A-chart complete-intersection presentation. -/
theorem _root_.solution :
    IsRegular (Ideal.Quotient.mk _
      (AdjoinRoot.of (canonicalAChartQuadratic25 K) (canonicalAChartBaseX25 K)) :
        CanonicalAChartTowerRing25 K) :=
  isRegular_scalar_mod_root_relation (canonicalAChartQuadratic25 K)
    (canonicalAChartLinearRemainder25 K) (canonicalAChartBaseX25 K)
    (canonicalAChartQuadratic25_monic K) X_ne_zero
    (canonicalAChartLinearRemainder25_mod_x_isRegular K)

local instance zSpecialization_semiring_sda1b5f : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

end N25
