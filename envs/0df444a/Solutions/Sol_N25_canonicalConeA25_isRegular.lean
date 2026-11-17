-- Prove2me | solution 1 for N25.canonicalConeA25_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:34.393201+00:00
-- url     : https://prove2.me/submissions/7ee8724a-8d79-43be-8089-3b06890a8043

import Mathlib
import Theorems.Thm_N25_canonicalConeBoundaryMap25_A
import Theorems.Thm_N25_canonicalConeTowerA25_isRegular
import Definitions.Def_N25_CanonicalConeTower
import Theorems.Thm_N25_isRegular_map_ringEquiv
import Definitions.Def_N25_CanonicalConeBoundary
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalConeTowerEquiv

/-! Explicit mutually inverse quotient maps between the literal cone and its monic presentation. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

/-- The normalizing linear form is regular in the actual literal cone. -/
theorem _root_.solution : IsRegular (canonicalConeA25 K) := by
  have h := isRegular_map_ringEquiv (canonicalConeTowerRingEquiv25 K) (canonicalConeTowerA25_isRegular K)
  change IsRegular (canonicalConeTowerToCone25 K
    (canonicalConeTowerProjection25 K (C (canonicalConeBaseA25 K)))) at h
  simpa only [canonicalConeTowerToCone25_projection, eval₂_C, canonicalConeBaseToCone25_A] using h

end N25
