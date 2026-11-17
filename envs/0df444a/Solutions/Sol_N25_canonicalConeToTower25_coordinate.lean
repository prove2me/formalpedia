-- Prove2me | solution 1 for N25.canonicalConeToTower25_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:03.881654+00:00
-- url     : https://prove2.me/submissions/c3e9914f-2f2a-44b0-b702-9b2cb4859486

import Mathlib
import Theorems.Thm_N25_canonicalConeBoundaryMap25_A
import Definitions.Def_N25_CanonicalConeTower
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

theorem _root_.solution (i : Fin 4) :
    canonicalConeToTower25 K (canonicalConeCoordinate25 K i) = canonicalConeTowerCoordinate25 K i := by
  simp [canonicalConeToTower25, canonicalConeCoordinate25, canonicalConeProjection25]

end N25
