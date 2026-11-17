-- Prove2me | solution 1 for N25.canonicalAChartTowerRingEquiv25_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:00.567744+00:00
-- url     : https://prove2.me/submissions/bdcd5cbe-0a3f-48ad-ba3a-ec3843b4c749

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

/-- The scalar multiplier in the monic tower is the literal affine multiplier. -/
theorem _root_.solution :
    canonicalAChartTowerRingEquiv25 K (Ideal.Quotient.mk _
      (AdjoinRoot.of (canonicalAChartQuadratic25 K) (canonicalAChartBaseMultiplier25 K))) =
    canonicalMultiplier (canonicalAChartCoordinate25 K 0) (canonicalAChartCoordinate25 K 1)
      (canonicalAChartCoordinate25 K 2) (canonicalAChartCoordinate25 K 3) := by
  change canonicalAChartTowerToChart25 K
    (canonicalAChartTowerProjection25 K (C (canonicalAChartBaseMultiplier25 K))) = _
  rw [canonicalAChartTowerToChart25_projection]
  simp only [eval₂_C, eval₂_add, eval₂_mul, canonicalAChartBaseMultiplier25, _root_.map_add, _root_.map_mul,
    canonicalAChartBaseToChart25_X, canonicalAChartBaseToChart25_Z,
    canonicalMultiplier, canonicalDenominator, canonicalAChartW25_eq]
  ring

end N25
