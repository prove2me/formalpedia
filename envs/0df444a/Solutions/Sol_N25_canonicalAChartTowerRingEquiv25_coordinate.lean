-- Prove2me | solution 1 for N25.canonicalAChartTowerRingEquiv25_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:27.464382+00:00
-- url     : https://prove2.me/submissions/ddd4fd36-b2f1-43b3-b3e3-74bf3067d70f

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalAChartTowerEquiv

/-! Explicit mutually inverse quotient maps between the literal cone and its monic presentation. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

/-- The monic presentation preserves every one of the four literal affine coordinates. -/
theorem _root_.solution (i : Fin 4) :
    canonicalAChartTowerRingEquiv25 K (canonicalAChartTowerCoordinate25 K i) =
      canonicalAChartCoordinate25 K i := by
  change canonicalAChartTowerToChart25 K (canonicalAChartTowerCoordinate25 K i) = _
  fin_cases i <;> simp [canonicalAChartTowerCoordinate25, canonicalAChartTowerToChart25_projection,
    canonicalAChartBaseToChart25_X, canonicalAChartBaseToChart25_Z, canonicalAChartW25_eq]

end N25
