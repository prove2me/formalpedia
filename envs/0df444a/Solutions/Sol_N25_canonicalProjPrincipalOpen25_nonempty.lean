-- Prove2me | solution 1 for N25.canonicalProjPrincipalOpen25_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:51.957311+00:00
-- url     : https://prove2.me/submissions/ca374027-8b48-4204-a876-261d38644c4e

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

/-! The principal-open germ identifies the actual scheme field with the literal fraction field. -/
noncomputable section

universe u

namespace N25

open AlgebraicGeometry CategoryTheory

variable (K : Type u) [Field K]

/-- The integral plane-open algebra supplies nonemptiness over every coefficient field. -/
theorem _root_.solution : Nonempty (canonicalProjPrincipalOpen25 K) := by
  letI : IsDomain (CanonicalOpenChartRing25 K) := canonicalOpenChartRing25C_isDomain
  let t : PrimeSpectrum (CanonicalProjPrincipalRing25 K) :=
    PrimeSpectrum.comap (canonicalPrincipalOpenAlgEquiv25 K).symm.toRingHom ⟨⊥, inferInstance⟩
  let f := Proj.awayι (canonicalConePiece25 K) (canonicalConePrincipalElement25 K)
    (canonicalConePrincipalElement25_mem K) (by decide : 0 < (5 : ℕ))
  refine ⟨⟨f.base t, ?_⟩⟩
  have ht : f.base t ∈ f.opensRange := ⟨t, rfl⟩
  simpa only [f, Proj.opensRange_awayι, canonicalProjPrincipalOpen25] using ht

variable [IsIntegral (CanonicalProjectiveCurve25 K)]

end N25

namespace N25

open AlgebraicGeometry CategoryTheory

end N25
