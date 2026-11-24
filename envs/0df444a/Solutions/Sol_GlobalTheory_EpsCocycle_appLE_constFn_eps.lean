-- Prove2me | solution 1 for GlobalTheory.EpsCocycle.appLE_constFn_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:44:49.176286+00:00
-- url     : https://prove2.me/submissions/c0cc8e28-04ab-404d-851d-23b8b7676b6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleCocycleOneAddEps

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
open GlobalTheory GlobalTheory.EpsCocycle
noncomputable section
namespace GlobalTheory.EpsCocycle
theorem _root_.solution {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)}
    {j : Y ⟶ Y'} (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    {O : Y.Opens} {O' : Y'.Opens} (h : O ≤ j ⁻¹ᵁ O') :
    (j.appLE O' O h).hom (constFn π O' DualNumber.eps) = 0 := by
  have h0 : O' ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  change (j.appLE O' O h).hom ((π.appLE ⊤ O' h0).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps)) = 0
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Sp (DualNumber ℂ))
      (_ : f = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (e : O ≤ f ⁻¹ᵁ ⊤),
      (f.appLE ⊤ O e).hom ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = 0 := by
    intro f hf e
    subst hf
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have e2 := congrArg (fun φ => φ.hom DualNumber.eps) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    have e3 : (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom DualNumber.eps = 0 := by
      simp
    rw [e3, map_zero] at e2
    exact (congrArg _ e2.symm).trans (map_zero _)
  exact key _ hq _
end GlobalTheory.EpsCocycle
