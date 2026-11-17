-- Prove2me | solution 1 for N25.canonicalConeRing25_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:09.201393+00:00
-- url     : https://prove2.me/submissions/3ef90dd7-7ac1-4ecd-80c9-71f71d96bc82

import Mathlib
import Theorems.Thm_N25_canonicalConeRing25_isDomain_of_regular
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
import Theorems.Thm_N25_canonicalConeA25_isRegular
import Theorems.Thm_N25_canonicalConeBoundaryMap25_A
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary
import Definitions.Def_N25_CanonicalConeTowerEquiv
import Theorems.Thm_N25_canonicalAChartRing25_isDomain
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
import Definitions.Def_N25_CanonicalAChartTowerEquiv
import Mathlib.AlgebraicGeometry.Properties
import Definitions.Def_N25_CanonicalProjectiveGenericPoint

/-! Reducedness and irreducibility of the literal Proj from its homogeneous cone. -/

noncomputable section

universe u

namespace N25

open AlgebraicGeometry HomogeneousLocalization

variable (K : Type u) [Field K]

/-- The full literal homogeneous cone is a domain over every coefficient field. -/
theorem _root_.solution : IsDomain (CanonicalConeRing25 K) := by
  letI := canonicalAChartRing25_isDomain K
  letI : IsDomain (CanonicalAProjRing25 K) :=
    Function.Injective.isDomain (canonicalAChartAlgEquiv25 K).symm.toRingHom
      (canonicalAChartAlgEquiv25 K).symm.injective
  exact canonicalConeRing25_isDomain_of_regular K (canonicalConeA25_isRegular K)

end N25
