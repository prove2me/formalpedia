-- Prove2me | solution 1 for N25.canonicalProjectiveCurve25_isIntegral_of_coneDomain
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:08.56223+00:00
-- url     : https://prove2.me/submissions/a61b55e9-f8ca-4642-b3a1-024210d42f59

import Mathlib
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalConePolynomial
import Theorems.Thm_N25_canonicalConeToTower25_coordinate
import Theorems.Thm_N25_canonicalConeBoundaryMap25_A
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary
import Definitions.Def_N25_CanonicalConeTowerEquiv
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
import Definitions.Def_N25_CanonicalAChartTowerEquiv
import Mathlib.AlgebraicGeometry.Properties
import Definitions.Def_N25_CanonicalProjectiveGenericPoint
import Theorems.Thm_N25_canonicalProjectiveCurve25_irreducibleSpace_of_coneDomain
import Theorems.Thm_N25_canonicalProjectiveCurve25_isReduced_of_coneDomain

/-! Reducedness and irreducibility of the literal Proj from its homogeneous cone. -/

noncomputable section

universe u

namespace N25

open AlgebraicGeometry HomogeneousLocalization

variable (K : Type u) [Field K]

/-- A domain cone with a nonzero normalizing coordinate gives an integral literal Proj. -/
theorem _root_.solution [IsDomain (CanonicalConeRing25 K)]
    (ha : canonicalConeA25 K ≠ 0) : IsIntegral (CanonicalProjectiveCurve25 K) := by
  letI := canonicalProjectiveCurve25_isReduced_of_coneDomain K
  letI := canonicalProjectiveCurve25_irreducibleSpace_of_coneDomain K ha
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end N25
