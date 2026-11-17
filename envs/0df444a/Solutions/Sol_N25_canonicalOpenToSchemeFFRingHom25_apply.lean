-- Prove2me | solution 1 for N25.canonicalOpenToSchemeFFRingHom25_apply
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:21.074991+00:00
-- url     : https://prove2.me/submissions/56233af0-d54c-4143-8da4-b7ad192e996f

import Mathlib
import Definitions.Def_N25_CanonicalSchemeFunctionField
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
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
import Theorems.Thm_N25_canonicalProjPrincipalOpen25_nonempty
import Definitions.Def_N25_canonicalOpenToSchemeFFRingHom25

/-! The principal-open germ identifies the actual scheme field with the literal fraction field. -/
noncomputable section

universe u

namespace N25

open AlgebraicGeometry CategoryTheory

variable (K : Type u) [Field K]

variable [IsIntegral (CanonicalProjectiveCurve25 K)]

theorem _root_.solution (r : CanonicalOpenChartRing25 K) :
    letI := canonicalProjPrincipalOpen25_nonempty K
    canonicalOpenToSchemeFFRingHom25 K r =
      (CanonicalProjectiveCurve25 K).germToFunctionField (canonicalProjPrincipalOpen25 K)
        (Proj.awayToSection (canonicalConePiece25 K) (canonicalConePrincipalElement25 K)
          (canonicalPrincipalOpenAlgEquiv25 K r)) := rfl

end N25

namespace N25

open AlgebraicGeometry CategoryTheory

end N25
