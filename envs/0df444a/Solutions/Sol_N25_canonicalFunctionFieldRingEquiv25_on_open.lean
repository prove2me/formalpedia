-- Prove2me | solution 1 for N25.canonicalFunctionFieldRingEquiv25_on_open
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:20.236239+00:00
-- url     : https://prove2.me/submissions/4cf6e399-d3a9-4af3-9952-41abfd02c4f8

import Mathlib
import Definitions.Def_N25_CanonicalSchemeFunctionField
import Theorems.Thm_N25_canonicalOpenChartRing25C_isDomain
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
import Definitions.Def_N25_canonicalOpenSectionsRingEquiv25
import Definitions.Def_N25_canonicalOpenToSchemeFFRingHom25
import Definitions.Def_N25_canonicalFunctionFieldRingEquiv25

/-! The principal-open germ identifies the actual scheme field with the literal fraction field. -/
noncomputable section

universe u

namespace N25

open AlgebraicGeometry CategoryTheory

variable (K : Type u) [Field K]

variable [IsIntegral (CanonicalProjectiveCurve25 K)]

/-- The selected field equivalence fixes every element of the literal principal open. -/
theorem _root_.solution (r : CanonicalOpenChartRing25 K) :
    canonicalFunctionFieldRingEquiv25 K (canonicalOpenToSchemeFFRingHom25 K r) =
      algebraMap (CanonicalOpenChartRing25 K) (CanonicalFF25 K) r := by
  letI := canonicalProjPrincipalOpen25_nonempty K
  letI := canonicalOpenChartRing25C_isDomain (K := K)
  letI : IsFractionRing
      Γ(CanonicalProjectiveCurve25 K, canonicalProjPrincipalOpen25 K) (CanonicalSchemeFF25 K) :=
    functionField_isFractionRing_of_isAffineOpen (CanonicalProjectiveCurve25 K)
      (canonicalProjPrincipalOpen25 K)
      (Proj.isAffineOpen_basicOpen (canonicalConePiece25 K) (canonicalConePrincipalElement25 K)
        (canonicalConePrincipalElement25_mem K) (by decide : 0 < (5 : ℕ)))
  change IsFractionRing.ringEquivOfRingEquiv (K := CanonicalSchemeFF25 K) (L := CanonicalFF25 K)
    (canonicalOpenSectionsRingEquiv25 K).symm
    (algebraMap Γ(CanonicalProjectiveCurve25 K, canonicalProjPrincipalOpen25 K)
      (CanonicalSchemeFF25 K) (canonicalOpenSectionsRingEquiv25 K r)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, RingEquiv.symm_apply_apply]

end N25

namespace N25

open AlgebraicGeometry CategoryTheory

end N25
