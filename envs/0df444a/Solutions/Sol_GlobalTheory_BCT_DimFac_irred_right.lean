-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.irred_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:09:38.735933+00:00
-- url     : https://prove2.me/submissions/3fb5c003-ea86-4f2a-98a3-1dc91a7f5097

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_contractLeft_map
import Theorems.Thm_GlobalTheory_BCT_DimFac_exists_dual_one
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractLeft_tmul
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_contractLeft_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_contractRight_ne_zero
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
theorem _root_.solution {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible) {σ : Representation ℂ Γ W}
    {τ : Representation ℂ Γ M} (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V) (hΦ : ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t)) :
    τ.IsIrreducible := by
  obtain ⟨hV, hV'⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have ht : Φ.symm v ≠ 0 := by simpa using hv
  obtain ⟨l₀, hl₀⟩ := exists_contractLeft_ne_zero ht
  obtain ⟨l₁, hl₁⟩ := exists_contractRight_ne_zero ht
  obtain ⟨l, hl⟩ := exists_dual_one hl₁
  set x := contractRight l₁ (Φ.symm v)
  refine (GlobalTheory.CuspRep.isIrreducible_iff τ).2 ⟨⟨_, _, hl₀⟩, fun N hN => ?_⟩
  let X : Submodule ℂ V := ⨅ l : Dual ℂ W, N.comap (contractLeft l ∘ₗ Φ.symm.toLinearMap)
  have hX : ∀ t, Φ t ∈ X ↔ ∀ l : Dual ℂ W, contractLeft l t ∈ N := fun t => by simp [X]
  rcases hV' X (fun g v hv => by
    obtain ⟨t, rfl⟩ := Φ.surjective v
    rw [← hΦ, hX]
    intro l
    rw [contractLeft_map]
    exact hN g _ ((hX t).1 hv _)) with h | h
  · refine Or.inl ((Submodule.eq_bot_iff _).2 fun m hm => ?_)
    have h1 : Φ (x ⊗ₜ m) ∈ X := (hX _).2 fun l => by
      rw [contractLeft_tmul]
      exact N.smul_mem _ hm
    rw [h, Submodule.mem_bot, map_eq_zero_iff _ Φ.injective] at h1
    have h2 := congrArg (contractLeft l) h1
    rwa [contractLeft_tmul, hl, one_smul, map_zero] at h2
  · refine Or.inr (Submodule.eq_top_iff'.2 fun m => ?_)
    have h2 := (hX (x ⊗ₜ m)).1 (h ▸ Submodule.mem_top) l
    rwa [contractLeft_tmul, hl, one_smul] at h2
end GlobalTheory.BCT.DimFac
