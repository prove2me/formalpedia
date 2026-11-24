-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.eq_zero_of_conv_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:18.636883+00:00
-- url     : https://prove2.me/submissions/cb8e21bf-4d1c-4809-bce9-847ffd5b5508

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
theorem _root_.solution {a : G → ℂ} (h : conv a (adj a) = 0) : a = 0 := by
  have h1 := congrFun h 1
  simp only [conv, adj, mul_one, inv_inv, Complex.mul_conj, Pi.zero_apply] at h1
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun y _ => Complex.normSq_nonneg _] at h1
  funext y
  exact Complex.normSq_eq_zero.mp (h1 y (Finset.mem_univ _))
end GlobalTheory.BadShare.Basic
