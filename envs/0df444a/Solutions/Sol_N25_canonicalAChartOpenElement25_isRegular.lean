-- Prove2me | solution 1 for N25.canonicalAChartOpenElement25_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:31.026039+00:00
-- url     : https://prove2.me/submissions/36d437b0-ce56-4b78-b7b6-97b249d17e99

import Mathlib
import Theorems.Thm_N25_canonicalAChartTowerX25_isRegular
import Theorems.Thm_N25_canonicalAChartTowerZ25_isRegular
import Theorems.Thm_N25_canonicalAChartTowerMultiplier25_isRegular
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_isRegular_map_ringEquiv
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
import Theorems.Thm_N25_canonicalAChartTowerRingEquiv25_coordinate
import Theorems.Thm_N25_canonicalAChartTowerRingEquiv25_multiplier
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

/-! Integrality of the literal normalized canonical chart. -/
noncomputable section

namespace N25

variable (K : Type*) [Field K]

/-- The localization denominator is regular in the actual affine-coordinate quotient. -/
theorem _root_.solution :
    IsRegular (canonicalAChartOpenElement25 K) := by
  have hxT : IsRegular (canonicalAChartTowerCoordinate25 K 0) :=
    canonicalAChartTowerX25_isRegular K
  have hzT : IsRegular (canonicalAChartTowerCoordinate25 K 2) :=
    canonicalAChartTowerZ25_isRegular K
  have hx := isRegular_map_ringEquiv (canonicalAChartTowerRingEquiv25 K) hxT
  have hz := isRegular_map_ringEquiv (canonicalAChartTowerRingEquiv25 K) hzT
  rw [canonicalAChartTowerRingEquiv25_coordinate] at hx hz
  have hB := isRegular_map_ringEquiv (canonicalAChartTowerRingEquiv25 K)
    (canonicalAChartTowerMultiplier25_isRegular K)
  rw [canonicalAChartTowerRingEquiv25_multiplier] at hB
  exact (hx.mul hz).mul hB

end N25
