-- Prove2me | solution 1 for N25.canonicalProjectiveCurve25_isIntegral_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:10.527921+00:00
-- url     : https://prove2.me/submissions/3b197072-047f-4427-9a85-b9e50c0daaa5

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
import Theorems.Thm_N25_canonicalProjectiveCurve25_isIntegral

/-! Reducedness and irreducibility of the literal Proj from its homogeneous cone. -/

noncomputable section

universe u

namespace N25

open AlgebraicGeometry HomogeneousLocalization

variable (K : Type u) [Field K]

/-- Good-prime specialization of integrality on the full selected projective model. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) (K : Type u) [Field K] [CharP K p] :
    IsIntegral (CanonicalProjectiveCurve25 K) :=
  canonicalProjectiveCurve25_isIntegral K

end N25
