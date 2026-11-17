-- Prove2me | solution 1 for N25.canonicalAChartTowerZ25_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:30.412259+00:00
-- url     : https://prove2.me/submissions/653863c7-b69d-4cee-8a1c-f59cb12ab710

import Mathlib
import Theorems.Thm_N25_canonicalAChartQuadratic25_monic
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_isRegular_scalar_mod_root_relation
import Theorems.Thm_N25_canonicalAChartLinearRemainder25_mod_z_isRegular

/-! Coordinate regularity in the monic presentation of the canonical A-chart. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance xSpecialization_semiring_sb11b45 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

local instance zSpecialization_semiring_sb11b45 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- z is regular in the A-chart complete-intersection presentation. -/
theorem _root_.solution :
    IsRegular (Ideal.Quotient.mk _
      (AdjoinRoot.of (canonicalAChartQuadratic25 K) (canonicalAChartBaseZ25 K)) :
        CanonicalAChartTowerRing25 K) :=
  isRegular_scalar_mod_root_relation (canonicalAChartQuadratic25 K)
    (canonicalAChartLinearRemainder25 K) (canonicalAChartBaseZ25 K)
    (canonicalAChartQuadratic25_monic K) (C_ne_zero.mpr X_ne_zero)
    (canonicalAChartLinearRemainder25_mod_z_isRegular K)

end N25
