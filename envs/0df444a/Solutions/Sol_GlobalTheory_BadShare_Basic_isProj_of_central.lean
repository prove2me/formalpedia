-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.isProj_of_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:46:47.346115+00:00
-- url     : https://prove2.me/submissions/2ef0e72a-e335-44cc-8684-8cc77eb4ace8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_alg_injective
import Theorems.Thm_GlobalTheory_BadShare_Basic_alg_conv
import Theorems.Thm_GlobalTheory_BadShare_Basic_adj_adj
import Theorems.Thm_GlobalTheory_BadShare_Basic_adj_conv
import Theorems.Thm_GlobalTheory_BadShare_Basic_eq_zero_of_conv_adj
import Theorems.Thm_GlobalTheory_BadShare_Basic_alg_sub

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
theorem _root_.solution {e : G → ℂ} (he : conv e e = e) (hc : ∀ a, conv e a = conv a e) : IsProj e := by
  have ha : conv (adj e) (adj e) = adj e := by rw [← adj_conv, he]
  have hE : alg e * alg e = alg e := by rw [← alg_conv, he]
  have hA : alg (adj e) * alg (adj e) = alg (adj e) := by rw [← alg_conv, ha]
  have hC : alg (adj e) * alg e = alg e * alg (adj e) := by rw [← alg_conv, ← hc, alg_conv]
  have h1 : adj (conv e (adj e)) = conv e (adj e) := by rw [adj_conv, adj_adj]
  have h2 : adj (e - conv e (adj e)) = adj e - conv e (adj e) := by
    conv_rhs => rw [← h1]
    funext x; simp [adj]
  have h3 : e - conv e (adj e) = 0 := by
    refine eq_zero_of_conv_adj (alg_injective ?_)
    rw [h2, alg_conv, alg_sub, alg_sub, alg_conv, show alg (0 : G → ℂ) = 0 by simp [alg], sub_mul, mul_sub, mul_sub,
      ← mul_assoc, hE, mul_assoc, hA, mul_assoc, ← mul_assoc (alg (adj e)), hC, mul_assoc, hA, ← mul_assoc, hE]
    simp
  have h4 : adj e = e := by rw [sub_eq_zero.mp h3, h1]
  refine ⟨he, fun x => ?_⟩
  conv_lhs => rw [← h4]
  simp [adj]
end GlobalTheory.BadShare.Basic
