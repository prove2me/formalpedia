-- Prove2me | solution 1 for N25.canonicalAChartToOpen25_injective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:31.704419+00:00
-- url     : https://prove2.me/submissions/e465b87d-5c23-4cd4-9965-ea1b79908b5f

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
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
import Theorems.Thm_N25_canonicalAChartOpenElement25_isRegular

/-! Integrality of the literal normalized canonical chart. -/
noncomputable section

namespace N25

variable (K : Type*) [Field K]

/-- The affine coordinate ring injects into its actual integral principal open. -/
theorem _root_.solution :
    Function.Injective (algebraMap (CanonicalAChartRing25 K) (CanonicalOpenChartRing25 K)) := by
  apply IsLocalization.injectiveₛ (M := Submonoid.powers (canonicalAChartOpenElement25 K))
    (CanonicalOpenChartRing25 K)
  rintro s ⟨n, rfl⟩
  exact (canonicalAChartOpenElement25_isRegular K).pow n

end N25
