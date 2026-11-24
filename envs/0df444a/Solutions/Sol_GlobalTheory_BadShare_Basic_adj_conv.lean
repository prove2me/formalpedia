-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.adj_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:00:20.493259+00:00
-- url     : https://prove2.me/submissions/c5b09c4e-b30b-4b76-b21d-a95f2ca8d5d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial

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
theorem _root_.solution (a b : G → ℂ) : adj (conv a b) = conv (adj b) (adj a) := by
  funext x
  simp only [adj, conv, map_sum, map_mul]
  rw [← Equiv.sum_comp (Equiv.mulLeft x⁻¹)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_comm, mul_assoc]
end GlobalTheory.BadShare.Basic
