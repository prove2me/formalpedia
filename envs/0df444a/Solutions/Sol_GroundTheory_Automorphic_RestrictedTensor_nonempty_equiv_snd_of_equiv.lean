-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.nonempty_equiv_snd_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:13.050816+00:00
-- url     : https://prove2.me/submissions/c07a9098-0575-40b0-b0a6-8a34ac3294ae

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_contractLeft_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractLeft_outerTensor
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_tmul_ne_zero_of
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nontrivial_of_irreducible
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_outerTensor_tmul
import Theorems.Thm_P2M_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_matrixCoeff_eq__99399df656ad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
  {V₁ V₂ V₁' V₂' : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₁'] [Module ℂ V₁'] [AddCommGroup V₂'] [Module ℂ V₂']
variable {π₁ : Representation ℂ M₁ V₁} {π₂ : Representation ℂ M₂ V₂}
  {π₁' : Representation ℂ M₁ V₁'} {π₂' : Representation ℂ M₂ V₂'}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (h₁ : π₁.IsIrreducible) (h₂ : π₂.IsIrreducible)
    (h₂' : π₂'.IsIrreducible) (Φ : (outerTensor π₁ π₂).Equiv (outerTensor π₁' π₂')) :
    Nonempty (π₂.Equiv π₂') := by
  haveI := h₂
  haveI := h₂'
  have := nontrivial_of_irreducible h₁
  have := nontrivial_of_irreducible h₂
  obtain ⟨u, hu⟩ := exists_ne (0 : V₁)
  obtain ⟨v, hv⟩ := exists_ne (0 : V₂)
  have hΦ : ∀ p z, Φ (outerTensor π₁ π₂ p z) = outerTensor π₁' π₂' p (Φ z) :=
    fun p z => Representation.IntertwiningMap.isIntertwining _ _ Φ.toIntertwiningMap p z
  have hy : Φ (u ⊗ₜ v) ≠ 0 := fun h =>
    tmul_ne_zero_of hu hv (Φ.toLinearEquiv.injective (h.trans (map_zero _).symm))
  obtain ⟨l₁, hl₁⟩ := exists_contractLeft_ne_zero hy
  obtain ⟨l₂, hl₂⟩ : ∃ l : Dual ℂ V₂', l (contractLeft l₁ (Φ (u ⊗ₜ v))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hl₁ ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)
  let μ : Dual ℂ V₂ := l₂ ∘ₗ contractLeft l₁ ∘ₗ Φ.toLinearEquiv.toLinearMap ∘ₗ
    TensorProduct.mk ℂ V₁ V₂ u
  refine nonempty_equiv_of_matrixCoeff_eq' (v := v) (l := μ)
    (w := contractLeft l₁ (Φ (u ⊗ₜ v))) (m := l₂) (fun b => ?_) ⟨1, ?_⟩
  · have : u ⊗ₜ[ℂ] π₂ b v = outerTensor π₁ π₂ (1, b) (u ⊗ₜ v) := by
      rw [outerTensor_tmul, map_one, Module.End.one_apply]
    show l₂ (contractLeft l₁ (Φ (u ⊗ₜ π₂ b v))) = _
    rw [this, hΦ, contractLeft_outerTensor]
  · show l₂ (contractLeft l₁ (Φ (u ⊗ₜ π₂ 1 v))) ≠ 0
    rwa [map_one, Module.End.one_apply]
end GroundTheory.Automorphic.RestrictedTensor
