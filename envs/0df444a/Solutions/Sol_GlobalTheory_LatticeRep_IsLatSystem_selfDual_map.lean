-- Prove2me | solution 1 for GlobalTheory.LatticeRep.IsLatSystem.selfDual_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:58:50.484789+00:00
-- url     : https://prove2.me/submissions/429271a1-72a7-4f04-b0a0-d144fc09a39b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSelfOfTrivial
import Theorems.Thm_GlobalTheory_LatticeRep_mem_map_iff

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
namespace IsLatSystem
theorem _root_.solution (h : IsLatSystem σ w γ W lam A ρ) (g : Γ) : SelfDual γ (A.map (ρ g)) := by
  obtain ⟨-, -, hA, -, hρ, -⟩ := h
  have e : ∀ x, ρ g (ρ g⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  intro x
  rw [mem_map_iff, hA]
  constructor
  · rintro hx _ ⟨a, ha, rfl⟩
    rw [← hx a ha, ← hρ g (ρ g⁻¹ x), e]
  · intro hx a ha
    rw [← hρ g, e]
    exact hx _ ⟨a, ha, rfl⟩
end IsLatSystem
end GlobalTheory.LatticeRep
