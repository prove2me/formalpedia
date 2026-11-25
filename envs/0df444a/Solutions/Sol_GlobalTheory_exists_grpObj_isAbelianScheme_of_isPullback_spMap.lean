-- Prove2me | solution 1 for GlobalTheory.exists_grpObj_isAbelianScheme_of_isPullback_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:05:57.697473+00:00
-- url     : https://prove2.me/submissions/54bc8c06-9cec-4854-af6f-5feaaf015def

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  intro R _ A _ g hA hg R' _ σ X' s' φ h
  have hsm : SmoothOfRelativeDimension g s' := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg
  let B := (Over.pullback (spMap σ)).obj A
  letI : GrpObj B := Functor.grpObjObj
  let e : B ≅ Over.mk s' := Over.isoMk h.isoPullback.symm (by simp [B])
  letI : GrpObj (Over.mk s') := GrpObj.ofIso e
  refine ⟨this, ?_, hsm⟩
  have hc := hA.comm
  have hcB : IsCommMonObj B := Functor.isCommMonObj_obj
  exact {
    comm := by
      constructor
      show (β_ _ _).hom ≫ ((e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom) = (e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc,
        ← Category.assoc (β_ B B).hom, IsCommMonObj.mul_comm]
    smooth := MorphismProperty.of_isPullback (P := @Smooth) h hA.smooth
    proper := MorphismProperty.of_isPullback (P := @IsProper) h hA.proper
    geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hA.geomConnected }
end GlobalTheory
