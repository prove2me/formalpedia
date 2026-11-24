-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.rk_reg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:09.258796+00:00
-- url     : https://prove2.me/submissions/2fcbef20-5c39-4305-9cbe-dfb66cea4c14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_conv_assoc
import Theorems.Thm_GlobalTheory_BadShare_Basic_op_reg
import Theorems.Thm_GlobalTheory_BadShare_Basic_trace_op_reg

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
variable (G : Type) [Group G] [Fintype G]
variable {G}
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (e : G → ℂ) (he : conv e e = e) : (rk (regFn G) e : ℂ) = Fintype.card G * e 1 := by
  have hi : IsIdempotentElem (op (regFn G) e) := by
    refine LinearMap.ext fun f => ?_
    rw [Module.End.mul_apply, op_reg, op_reg, ← conv_assoc, he]
  rw [← trace_op_reg]
  exact ((LinearMap.IsIdempotentElem.isProj_range _ hi).trace).symm
end GlobalTheory.BadShare.Basic
