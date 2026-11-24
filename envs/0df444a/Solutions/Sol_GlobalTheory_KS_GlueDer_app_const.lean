-- Prove2me | solution 1 for GlobalTheory.KS.GlueDer.app_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:27:13.380887+00:00
-- url     : https://prove2.me/submissions/9e9f5c05-c7b3-4028-a5e4-d726ade641ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGlobalLocDerOfIsCob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.GlueDer
namespace GlobalTheory.KS.GlueDer
theorem _root_.solution {R K : Type} [CommRing R] [CommRing K] {X Y : Scheme.{0}} (x₀ : R →+* K) (p : X ⟶ Sp R)
    (q : Y ⟶ Sp K) (m : Y ⟶ X) (hm : m ≫ p = q ≫ spMap x₀) (U : X.Opens) (a : R) :
    (m.app U).hom (constFn p U a) = constFn q (m ⁻¹ᵁ U) (x₀ a) := by
  have h1 : (m.app U).hom (constFn p U a) = constFn (m ≫ p) (m ⁻¹ᵁ U) a := by
    simp only [constFn]
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE m p ⊤ U (m ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl)
  rw [h1, hm]
  simp only [constFn]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (x₀ a) =
      ((spMap x₀).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x₀)
    exact congrArg (fun φ => φ.hom a) this
  rw [h2]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.comp_appLE q (spMap x₀) ⊤ (m ⁻¹ᵁ U) (fun _ _ => trivial))
end GlobalTheory.KS.GlueDer
