-- Prove2me | solution 1 for GlobalTheory.monoToPowGr_injective_iff_lTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:07.77727+00:00
-- url     : https://prove2.me/submissions/db22c867-1e43-469e-bc8a-735411be553b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_powGr_toQuot_injective
import Theorems.Thm_GlobalTheory_monoToQuotPow_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution (f : ι → R) (a : ℕ) :
    Function.Injective (monoToPowGr M f a) ↔
      Function.Injective ((monoToQuotPow f a).lTensor M) := by
  classical
  set I := Ideal.span (Set.range f) with hI
  let e₁ : M ⊗[R] (MonoDeg ι a → R ⧸ I) ≃ₗ[R] (MonoDeg ι a → M ⧸ (I • ⊤ : Submodule R M)) :=
    TensorProduct.piRight R R M _ ≪≫ₗ
      LinearEquiv.piCongrRight fun _ => TensorProduct.tensorQuotEquivQuotSMul M I
  let e₂ := TensorProduct.tensorQuotEquivQuotSMul M (I ^ (a + 1))
  have hsq : e₂.toLinearMap ∘ₗ (monoToQuotPow f a).lTensor M =
      (powGr.toQuot I M a ∘ₗ (monoToPowGr M f a).restrictScalars R) ∘ₗ e₁.toLinearMap := by
    refine TensorProduct.ext' fun m c => ?_
    choose d hd using fun α => Ideal.Quotient.mk_surjective (c α)
    obtain rfl : c = fun α => Ideal.Quotient.mk I (d α) := funext fun α => (hd α).symm
    have h1 : e₁ (m ⊗ₜ fun α => Ideal.Quotient.mk I (d α)) =
        fun α => Submodule.Quotient.mk (d α • m) := by
      funext α
      exact TensorProduct.tensorQuotEquivQuotSMul_tmul_mk I m (d α)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, LinearMap.lTensor_tmul,
      LinearMap.restrictScalars_apply]
    rw [monoToQuotPow_mk, monoToPowGr_mk, powGr.toQuot_mk]
    refine (TensorProduct.tensorQuotEquivQuotSMul_tmul_mk _ m _).trans ?_
    simp [Finset.sum_smul, mul_smul]
  have hfun : e₂ ∘ (monoToQuotPow f a).lTensor M =
      (powGr.toQuot I M a ∘ monoToPowGr M f a) ∘ e₁ := congrArg DFunLike.coe hsq
  rw [← e₂.injective.of_comp_iff, hfun, Function.Injective.of_comp_iff' _ e₁.bijective,
    (powGr.toQuot_injective I M a).of_comp_iff]
end GlobalTheory
