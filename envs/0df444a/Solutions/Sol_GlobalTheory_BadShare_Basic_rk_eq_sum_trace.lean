-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.rk_eq_sum_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:16.811051+00:00
-- url     : https://prove2.me/submissions/27b4877c-3d8c-4ebf-89cc-ec287f563992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_op_conv

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
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M)
    {e : G → ℂ} (he : conv e e = e) : (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  have hi : IsIdempotentElem (op ρ e) := by rw [IsIdempotentElem, ← op_conv, he]
  rw [rk, ← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace]
  simp [op]
end GlobalTheory.BadShare.Basic
