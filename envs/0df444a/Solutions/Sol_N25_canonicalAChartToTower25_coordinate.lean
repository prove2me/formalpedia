-- Prove2me | solution 1 for N25.canonicalAChartToTower25_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:43.833548+00:00
-- url     : https://prove2.me/submissions/7178d19b-2c58-4a04-837e-d78f4260c36d

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

theorem _root_.solution (i : Fin 4) :
    canonicalAChartToTower25 K (canonicalAChartCoordinate25 K i) = canonicalAChartTowerCoordinate25 K i := by
  simp [canonicalAChartToTower25, canonicalAChartCoordinate25, canonicalAChartProjection25]

end N25
