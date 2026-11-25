-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.finrank_pos_of_countAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:26:58.730227+00:00
-- url     : https://prove2.me/submissions/a8b1ba45-1c6f-46f9-b2d3-fc4397286c49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_isProj_dirac

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
    {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) {ep : ℝ}
    (hep : ep < 1) (h : CountAt ρ ep) : 0 < Module.finrank ℂ M := by
  obtain ⟨c, hc, h⟩ := h
  have h1 := h dirac isProj_dirac (Or.inl fun γ hγ v => by
    have : γ = 1 := by by_contra h'; simp [dirac, h'] at hγ
    subst this
    simp)
  have h2 : op ρ dirac = 1 := by simp [op, dirac]
  have h3 : rk ρ dirac = Module.finrank ℂ M := by
    rw [rk, h2, Module.End.one_eq_id, LinearMap.range_id, finrank_top]
  rw [h3] at h1
  simp only [dirac, if_true, Complex.one_re, mul_one] at h1
  by_contra h0
  have : Module.finrank ℂ M = 0 := by omega
  rw [this, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hc] at h1
  nlinarith
end GlobalTheory.BadShare.Basic
