-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.HasComp.exists_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:30:08.264095+00:00
-- url     : https://prove2.me/submissions/48b03963-ce69-4de2-b23b-9ee5c1edf609

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_map_smulRight
import Theorems.Thm_GlobalTheory_BCT_DimFac_exists_split
import Theorems.Thm_GlobalTheory_BCT_DimFac_exists_dual_one
import Theorems.Thm_GlobalTheory_BCT_DimFac_map_left_of_fixed
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
theorem _root_.solution {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible) {e : Γ →* Γ}
    (he : ∀ g, e (e g) = e g) (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y)) {L : Subgroup Γ} (h : HasComp ρ e L 1) :
    ∃ P : V →ₗ[ℂ] V, (∀ g, e g = 1 → ∀ v, P (ρ g v) = ρ g (P v)) ∧
      ∀ v, (∀ g ∈ L, ρ (e g) v = v) → P v = v ∧ ∀ y, ∃ c : ℂ, P (ρ (e y) v) = c • v := by
  obtain ⟨W, _, _, σ, h1, h2, h3, ⟨f, hf0, hf⟩, h4⟩ := h
  obtain ⟨M, _, _, τ, Φ, hτ, hΦ⟩ := exists_split hρ h1 h2 he hc hf0 hf
  obtain ⟨x, hx0, hx⟩ := finrank_eq_one_iff'.1 h4
  obtain ⟨l, hl⟩ := exists_dual_one (x := x.1) fun h => hx0 (Subtype.ext h)
  refine ⟨Φ.toLinearMap ∘ₗ TensorProduct.map (l.smulRight x.1) LinearMap.id ∘ₗ Φ.symm.toLinearMap,
    fun g hg v => ?_, fun v hv => ?_⟩
  · obtain ⟨t, rfl⟩ := Φ.surjective v
    have : σ g = LinearMap.id := by rw [← h3, hg, map_one]; rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hΦ, ← hΦ, Φ.symm_apply_apply, Φ.symm_apply_apply, this]
    simp only [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp]
  · obtain ⟨t, rfl⟩ := Φ.surjective v
    have h5 : ∀ g ∈ L, TensorProduct.map (σ g) LinearMap.id t = t := fun g hg => by
      have := Φ.injective ((hΦ (e g) t).trans (hv g hg))
      rwa [h3, hτ] at this
    have h6 := map_left_of_fixed h5 (l.smulRight x.1) fun y hy => by
      obtain ⟨c, hc⟩ := hx ⟨y, hy⟩
      have : y = c • x.1 := (congrArg Subtype.val hc).symm
      simp [this, hl]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    refine ⟨by rw [Φ.symm_apply_apply, h6], fun y => ⟨l (σ y x.1), ?_⟩⟩
    have h7 : t = x.1 ⊗ₜ contractLeft l t := by rw [← map_smulRight, h6]
    rw [← hΦ, Φ.symm_apply_apply, h3, hτ, ← map_smul, h7]
    simp [TensorProduct.smul_tmul']
end HasComp
end GlobalTheory.BCT.DimFac
