-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.countAt_of_trace_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:34:35.971929+00:00
-- url     : https://prove2.me/submissions/13ce0d51-08f8-4db3-b0ab-fadb45d184aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_rk_eq_sum_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution {g₁ g₂ N : ℕ} [Fact g₁.Prime] [Fact g₂.Prime] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]
    (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M)
    (h : ∀ γ, γ ≠ 1 → AllUnip γ.1 ∨ AllUnip γ.2 → LinearMap.trace ℂ M (ρ γ) = 0) : CountAt ρ 0 := by
  refine ⟨Module.finrank ℂ M, by exact_mod_cast Module.finrank_pos, fun e he hu => ?_⟩
  have h1 := rk_eq_sum_trace ρ he.1
  rw [Finset.sum_eq_single 1, map_one, LinearMap.trace_one, mul_comm] at h1
  · have h2 := congrArg Complex.re h1
    rw [Complex.natCast_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at h2
    rw [h2]; simp
  · intro γ _ hγ
    by_cases h0 : e γ = 0
    · rw [h0, zero_mul]
    · rw [h γ hγ (hu.imp (fun H => H γ h0) fun H => H γ h0), mul_zero]
  · simp
end GlobalTheory.BadShare.Basic
