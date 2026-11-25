-- Prove2me | solution 1 for GlobalTheory.PermutationExistence.exists_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:01:09.678508+00:00
-- url     : https://prove2.me/submissions/f8e3929d-f7c9-40a7-9f87-4aec9b5ed383

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsRest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.PermutationExistence
namespace GlobalTheory.PermutationExistence
theorem _root_.solution {G : Type u_1} {C : Type u_2} [Group G] [AddCommMonoid C]
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (h : G) (hh : h ∈ H) :
    ∃ σ : G → G, (∀ s ∈ S, σ s ∈ S ∧ (σ s)⁻¹ * (h * s) ∈ V) ∧
      ∀ f : G → C, ∑ s ∈ S, f (σ s) = ∑ s ∈ S, f s := by
  classical
  have key : ∀ s ∈ S, ∃ s' : G, s' ∈ S ∧ s'⁻¹ * (h * s) ∈ V := fun s hs =>
    (hT (h * s) (H.mul_mem hh (hS s hs))).exists
  choose! σ hσS hσV using key
  refine ⟨σ, fun s hs => ⟨hσS s hs, hσV s hs⟩, fun f => ?_⟩

  have hinj : Set.InjOn σ S := by
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 := hσV s₁ hs₁
    rw [heq] at h1
    have h12 : s₁⁻¹ * s₂ ∈ V := by
      have e : ((σ s₂)⁻¹ * (h * s₁))⁻¹ * ((σ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ := by group
      rw [← e]
      exact V.mul_mem (V.inv_mem h1) (hσV s₂ hs₂)
    obtain ⟨u, _, hu⟩ := hT s₂ (hS s₂ hs₂)
    have e1 : s₁ = u := hu s₁ ⟨hs₁, h12⟩
    have e2 : s₂ = u := hu s₂ ⟨hs₂, by rw [inv_mul_cancel]; exact V.one_mem⟩
    rw [e1, e2]
  have himg : S.image σ = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact hσS s hs
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ s ∈ S, f (σ s) = ∑ x ∈ S.image σ, f x := (Finset.sum_image hinj).symm
    _ = ∑ s ∈ S, f s := by rw [himg]
end GlobalTheory.PermutationExistence
