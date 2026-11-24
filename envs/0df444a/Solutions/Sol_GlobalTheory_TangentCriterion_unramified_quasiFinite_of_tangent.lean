-- Prove2me | solution 1 for GlobalTheory.TangentCriterion.unramified_quasiFinite_of_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:42:22.623596+00:00
-- url     : https://prove2.me/submissions/10a614a4-6a88-4718-9027-cbd9b9c466b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnramifiedQuasiFiniteOfTangent
import Theorems.Thm_GlobalTheory_TangentCriterion_formallyUnramified_of_tangent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.TangentCriterion
namespace GlobalTheory.TangentCriterion
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f → (∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ X), x ≫ f = constPt x ≫ f → x = constPt x) → FormallyUnramified f ∧ LocallyQuasiFinite f := by
  intro X Y f hf h
  have key : ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
      (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.FormallyUnramified := by
    intro U hU V hV e
    have hft := f.finiteType_appLE hU hV e
    letI := (f.appLE U V e).hom.toAlgebra
    haveI : Algebra.FiniteType Γ(Y, U) Γ(X, V) := hft
    refine formallyUnramified_of_tangent (A := Γ(Y, U)) (B := Γ(X, V)) fun K _ g hg => ?_
    have hc : constPt (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) =
        Spec.map (CommRingCat.ofHom (((algebraMap K (DualNumber K)).comp
          (TrivSqZeroExt.fstHom K K K).toRingHom).comp g)) ≫ hV.fromSpec := by
      simp only [constPt, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have := h K (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) (by
      rw [hc]
      simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV e, ← Spec.map_comp_assoc]
      congr 2
      exact CommRingCat.hom_ext hg)
    rw [hc, cancel_mono, Spec.map_inj] at this
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨⟨key⟩, ⟨fun {U} hU {V} hV e => ?_⟩⟩
  have h1 := key hU hV e
  have hft := f.finiteType_appLE hU hV e
  letI := (f.appLE U V e).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Y, U) Γ(X, V) := hft
  haveI : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) := h1
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))
end GlobalTheory.TangentCriterion
