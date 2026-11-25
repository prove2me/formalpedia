-- Prove2me | solution 1 for GlobalTheory.LatticeRep.IsLatRep.exists_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:58:48.821031+00:00
-- url     : https://prove2.me/submissions/46e31a6e-e058-4f46-8811-2a5a427a2b01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSelfOfTrivial
import Theorems.Thm_GlobalTheory_LatticeRep_transl_induction
import Theorems.Thm_GlobalTheory_LatticeRep_IsLatRep_fix_of_map_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeRep
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}
namespace GlobalTheory.LatticeRep
namespace IsLatRep
theorem _root_.solution (h : IsLatSystem σ w γ W lam A ρ) (hO : IsLatRep W lam A ρ Om) (m : M) :
    ∃ s : Set X, s.Finite ∧ ∀ g, A.map (ρ g) ≤ A → (∀ x ∈ s, ρ g x - x ∈ A ∧ γ (w • x) (ρ g x - x) = 1) → Om g m = m := by
  refine transl_induction h.2.2.2.1 (p := fun m => ∃ s : Set X, s.Finite ∧ ∀ g, A.map (ρ g) ≤ A →
    (∀ x ∈ s, ρ g x - x ∈ A ∧ γ (w • x) (ρ g x - x) = 1) → Om g m = m) (fun x v hv => ?_)
    ⟨∅, Set.finite_empty, fun g _ _ => map_zero _⟩ (fun a b ha hb => ?_) (fun c a ha => ?_) m
  · refine ⟨{x}, Set.finite_singleton x, fun g hg hx => ?_⟩
    obtain ⟨h1, h2⟩ := hx x rfl
    have h3 := h.1.comp x (ρ g x - x) v
    rw [hv _ h1, h2, one_smul, add_sub_cancel] at h3
    rw [hO.1, hO.fix_of_map_le h hg hv, h3]
  · obtain ⟨s, hs, h1⟩ := ha
    obtain ⟨t, ht, h2⟩ := hb
    exact ⟨s ∪ t, hs.union ht, fun g hg hx => by
      rw [map_add, h1 g hg fun x hx' => hx x (Or.inl hx'), h2 g hg fun x hx' => hx x (Or.inr hx')]⟩
  · obtain ⟨s, hs, h1⟩ := ha
    exact ⟨s, hs, fun g hg hx => by rw [map_smul, h1 g hg hx]⟩
end IsLatRep
end GlobalTheory.LatticeRep
