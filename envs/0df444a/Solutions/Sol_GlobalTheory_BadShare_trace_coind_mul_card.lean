-- Prove2me | solution 1 for GlobalTheory.BadShare.trace_coind_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:16:00.325818+00:00
-- url     : https://prove2.me/submissions/751d5e8d-fa93-4dad-993a-22a5b92f5d58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
import Theorems.Thm_GlobalTheory_BadShare_trace_compLeft_funLeft
import Theorems.Thm_GlobalTheory_BadShare_coindSum_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
noncomputable section
open GlobalTheory GlobalTheory.BadShare
variable {G : Type} [Group G] [Fintype G] {Γ : Type} [Group Γ] [Fintype Γ] (r : Γ →* G)
  {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ Γ W)
namespace GlobalTheory.BadShare
theorem _root_.solution (g : G) :
    LinearMap.trace ℂ _ (Representation.coind r σ g) * (Fintype.card Γ : ℂ) =
      ∑ γ : Γ, ∑ x : G, if r γ * (x * g) = x then LinearMap.trace ℂ W (σ γ⁻¹) else 0 := by
  have h1 : (Fintype.card Γ : ℂ) • (Representation.coind r σ g : _ →ₗ[ℂ] _) =
      coindSum r σ ∘ₗ (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    rw [LinearMap.comp_apply, coindSum_apply]
    have : ∀ γ : Γ, σ γ⁻¹ ((LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) φ (r γ * x))
        = φ.1 (x * g) := by
      intro γ
      change σ γ⁻¹ (φ.1 (r γ * x * g)) = _
      rw [mul_assoc, φ.2 γ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [Finset.sum_congr rfl fun γ _ => this γ, Finset.sum_const, Finset.card_univ]
    change (Fintype.card Γ : ℂ) • φ.1 (x * g) = _
    rw [Nat.cast_smul_eq_nsmul]
  have h2 : (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) ∘ₗ coindSum r σ =
      ∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * (x * g) := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    change (coindSum r σ φ).1 (x * g) = _
    rw [coindSum_apply]
    simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]
  rw [mul_comm, ← smul_eq_mul, ← map_smul, h1, LinearMap.trace_comp_comm', h2, map_sum]
  exact Finset.sum_congr rfl fun γ _ => trace_compLeft_funLeft _ _
end GlobalTheory.BadShare
