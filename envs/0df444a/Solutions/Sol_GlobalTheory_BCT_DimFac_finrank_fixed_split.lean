-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.finrank_fixed_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:30:10.824189+00:00
-- url     : https://prove2.me/submissions/3a12bd22-5c55-41ac-bc35-e26611122ee0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_mem_fix
import Theorems.Thm_GlobalTheory_BCT_DimFac_map_left_of_fixed
import Theorems.Thm_GlobalTheory_BCT_DimFac_map_right_of_fixed
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
theorem _root_.solution {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ M}
    (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V) (hΦ : ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t)) {e : Γ →* Γ}
    (hσ : ∀ g, σ (e g) = σ g) (hτ : ∀ g, τ (e g) = 1) {L : Subgroup Γ} (hL : ∀ g ∈ L, e g ∈ L) :
    finrank ℂ (fixed ρ L) = finrank ℂ (fixed σ L) * finrank ℂ (fixed τ L) := by
  let j := TensorProduct.map (fixed σ L).subtype (fixed τ L).subtype
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat _ _ (Submodule.injective_subtype _) (Submodule.injective_subtype _)
  have hr : fixed ρ L = (LinearMap.range j).map Φ.toLinearMap := by
    refine le_antisymm (fun v hv => ?_) ?_
    · obtain ⟨t, rfl⟩ := Φ.surjective v
      have h0 : ∀ g ∈ L, TensorProduct.map (σ g) (τ g) t = t := fun g hg =>
        Φ.injective ((hΦ g t).trans (mem_fix.1 hv g hg))
      have h1 : ∀ g ∈ L, TensorProduct.map (σ g) LinearMap.id t = t := fun g hg => by
        have := h0 _ (hL g hg)
        rwa [hσ, hτ] at this
      have h2 : ∀ g ∈ L, TensorProduct.map LinearMap.id (τ g) t = t := fun g hg => by
        have := h0 _ (L.mul_mem (L.inv_mem (hL g hg)) hg)
        rwa [map_mul, map_mul, ← map_inv e, hσ, hτ, one_mul, ← map_mul, inv_mul_cancel, map_one] at this
      obtain ⟨p, hp⟩ := (fixed σ L).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
      obtain ⟨q, hq⟩ := (fixed τ L).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
      have h3 := map_left_of_fixed h1 ((fixed σ L).subtype ∘ₗ p) fun x hx =>
        congrArg Subtype.val (LinearMap.congr_fun hp ⟨x, hx⟩)
      have h4 := map_right_of_fixed h2 ((fixed τ L).subtype ∘ₗ q) fun x hx =>
        congrArg Subtype.val (LinearMap.congr_fun hq ⟨x, hx⟩)
      refine ⟨t, ⟨TensorProduct.map p q t, ?_⟩, rfl⟩
      conv_rhs => rw [← h3, ← h4]
      simp only [j, TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp]
    · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      refine mem_fix.2 fun g hg => ?_
      change ρ g (Φ (j t)) = Φ (j t)
      rw [← hΦ]
      congr 1
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [j, mem_fix.1 x.2 g hg, mem_fix.1 y.2 g hg]
      | add x y hx hy => simp only [map_add, hx, hy]
  rw [hr, LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj hj, Module.finrank_tensorProduct]
end GlobalTheory.BCT.DimFac
