-- Prove2me | solution 1 for GlobalTheory.IsotypicOrth.left_ker_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:31.360619+00:00
-- url     : https://prove2.me/submissions/b0cb3124-3e25-4297-ba3c-7c61af81dbbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsComplOrthogonalOfNoCommonIrreducibleTypes
import Theorems.Thm_GlobalTheory_IsotypicOrth_pair_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.IsotypicOrth
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
  {σ : K →* K}
namespace GlobalTheory.IsotypicOrth
theorem _root_.solution (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x = 0 := by
  let T : Subrepresentation ρ :=
    ⟨S₁.toSubmodule ⊓ ⨅ y ∈ S.toSubmodule, LinearMap.ker (B.flip y), by
      intro k x hx
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.flip_apply] at hx ⊢
      refine ⟨S₁.apply_mem_toSubmodule k hx.1, fun y hy => ?_⟩
      rw [pair_left B hB]
      exact hx.2 _ (S.apply_mem_toSubmodule _ hy)⟩
  have hle : T ≤ S₁ := fun x hx => (Submodule.mem_inf.mp hx).1
  have hmem : ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x ∈ T.toSubmodule := by
    intro x hx h0
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    exact ⟨hx, h0⟩
  rcases h₁.le_iff.mp hle with h | h
  · intro x hx h0
    have hT : T.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    have := hmem x hx h0
    rw [hT] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exfalso
    obtain ⟨x, hx, y, hy, hne⟩ := hn
    have hT : T.toSubmodule = S₁.toSubmodule := congrArg Subrepresentation.toSubmodule h
    rw [← hT] at hx
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.flip_apply] at hx
    exact hne (hx.2 y hy)
end GlobalTheory.IsotypicOrth
