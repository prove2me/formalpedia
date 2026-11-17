-- Prove2me | solution 1 for N25.canonicalOpenToSchemeFFRingHom25_commutes
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:21.725659+00:00
-- url     : https://prove2.me/submissions/40699e98-ba54-4ba4-872a-e99f507af0ed

import Mathlib
import Definitions.Def_N25_CanonicalSchemeFunctionField
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Theorems.Thm_N25_canonicalProjScalarSection25
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
import Theorems.Thm_N25_canonicalOpenToSchemeFFRingHom25_apply
import Theorems.Thm_N25_canonicalProjPrincipalOpen25_nonempty
import Definitions.Def_N25_canonicalOpenToSchemeFFRingHom25

/-! The principal-open germ identifies the actual scheme field with the literal fraction field. -/
noncomputable section

universe u

namespace N25

open AlgebraicGeometry CategoryTheory

variable (K : Type u) [Field K]

variable [IsIntegral (CanonicalProjectiveCurve25 K)]

/-- The exact open germ respects the coefficient action defined by the structure morphism. -/
theorem _root_.solution (a : K) :
    canonicalOpenToSchemeFFRingHom25 K (algebraMap K (CanonicalOpenChartRing25 K) a) =
      algebraMap K (CanonicalSchemeFF25 K) a := by
  letI := canonicalProjPrincipalOpen25_nonempty K
  have hs := canonicalProjScalarSection25 K (canonicalConePrincipalElement25 K)
    (canonicalConePrincipalElement25_mem K) (by decide : 0 < (5 : ℕ))
  have hsa := congrArg
    (fun f : CommRingCat.of K ⟶ Γ(CanonicalProjectiveCurve25 K, canonicalProjPrincipalOpen25 K) => f a) hs
  have hsec : Proj.awayToSection (canonicalConePiece25 K) (canonicalConePrincipalElement25 K)
      (algebraMap K (CanonicalProjPrincipalRing25 K) a) =
      (canonicalProjectiveCurveToSpec25 K).appLE ⊤ (canonicalProjPrincipalOpen25 K) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) := hsa
  rw [canonicalOpenToSchemeFFRingHom25_apply, (canonicalPrincipalOpenAlgEquiv25 K).commutes, hsec]
  change (CanonicalProjectiveCurve25 K).germToFunctionField (canonicalProjPrincipalOpen25 K)
      ((canonicalProjectiveCurveToSpec25 K).appLE ⊤ (canonicalProjPrincipalOpen25 K) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) = canonicalSchemeFF25_baseMap K a
  simp only [canonicalSchemeFF25_baseMap, Scheme.Hom.appLE, Scheme.germToFunctionField,
    CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

end N25

namespace N25

open AlgebraicGeometry CategoryTheory

end N25
