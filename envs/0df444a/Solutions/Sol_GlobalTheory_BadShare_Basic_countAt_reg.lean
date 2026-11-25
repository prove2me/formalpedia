-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.countAt_reg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:34:29.541075+00:00
-- url     : https://prove2.me/submissions/0b7fc3e4-828b-4802-ba2b-05e8627f5914

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_rk_reg

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
theorem _root_.solution {g₁ g₂ N : ℕ} [Fact g₁.Prime] [Fact g₂.Prime] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] :
    CountAt (regFn ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N))) 0 := by
  refine ⟨Fintype.card ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)), by exact_mod_cast Fintype.card_pos, fun e he _ => ?_⟩
  have h := congrArg Complex.re (rk_reg e he.1)
  rw [Complex.natCast_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at h
  rw [h]
  simp
end GlobalTheory.BadShare.Basic
