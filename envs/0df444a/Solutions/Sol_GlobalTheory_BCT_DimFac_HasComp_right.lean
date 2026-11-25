-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.HasComp.right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:53.410602+00:00
-- url     : https://prove2.me/submissions/12dd6dce-e3d9-4306-953d-e0bd5af85c1e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_contractLeft_map
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_contractLeft_ne_zero
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.BCT.DimFac
namespace HasComp
theorem _root_.solution {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ M}
    (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V) (hΦ : ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t)) {e : Γ →* Γ}
    (hσ : ∀ g, σ (e g) = 1) {L : Subgroup Γ} {d : ℕ} (h : HasComp ρ e L d) : HasComp τ e L d := by
  obtain ⟨W', _, _, σ', h1, h2, h3, ⟨f, hf0, hf⟩, h4⟩ := h
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  obtain ⟨l, hl⟩ := exists_contractLeft_ne_zero (z := Φ.symm (f x)) (by simpa using hx)
  refine ⟨W', _, _, σ', h1, h2, h3, ⟨contractLeft l ∘ₗ Φ.symm.toLinearMap ∘ₗ f, fun h => hl (LinearMap.congr_fun h x),
    fun g y => ?_⟩, h4⟩
  obtain ⟨t, ht⟩ := Φ.surjective (f y)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hf, ← ht, ← hΦ, Φ.symm_apply_apply, Φ.symm_apply_apply, contractLeft_map, hσ]
  rfl
end HasComp
end GlobalTheory.BCT.DimFac
