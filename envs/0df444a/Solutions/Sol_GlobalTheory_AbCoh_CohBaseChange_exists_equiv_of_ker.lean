-- Prove2me | solution 1 for GlobalTheory.AbCoh.CohBaseChange.exists_equiv_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:31:01.633967+00:00
-- url     : https://prove2.me/submissions/a8cb0800-3d01-4ce9-b37f-1f49916aa641

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpMapAlgHomAlgebraMap
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
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.CohBaseChange
namespace GlobalTheory.AbCoh.CohBaseChange
theorem _root_.solution {S M A B : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup A]
    [Module S A] [AddCommGroup B] [Module S B] (f : M →ₗ[S] A) (g : M →ₗ[S] B) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : ∀ z, f z = 0 ↔ g z = 0) : ∃ e : A ≃ₗ[S] B, ∀ z, e (f z) = g z := by
  have hk : LinearMap.ker f = LinearMap.ker g := by
    ext z; exact h z
  refine ⟨(f.quotKerEquivOfSurjective hf).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    g.quotKerEquivOfSurjective hg, fun z ↦ ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f z) = Submodule.Quotient.mk z := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearEquiv.trans_apply, this]
  rfl
end GlobalTheory.AbCoh.CohBaseChange
