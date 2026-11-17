-- Prove2me | solution 1 for N25.canonicalAChartRing25_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:32.388855+00:00
-- url     : https://prove2.me/submissions/3cf9b6c4-7b03-47a3-bd28-200f38992472

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Theorems.Thm_N25_canonicalOpenChartRing25C_isDomain
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalAChartTowerEquiv
import Theorems.Thm_N25_canonicalAChartToOpen25_injective

/-! Integrality of the literal normalized canonical chart. -/
noncomputable section

namespace N25

variable (K : Type*) [Field K]

/-- The literal A=1 canonical affine chart is a domain over every field. -/
theorem _root_.solution : IsDomain (CanonicalAChartRing25 K) := by
  letI := canonicalOpenChartRing25C_isDomain (K := K)
  exact Function.Injective.isDomain
    (algebraMap (CanonicalAChartRing25 K) (CanonicalOpenChartRing25 K))
    (canonicalAChartToOpen25_injective K)

end N25
