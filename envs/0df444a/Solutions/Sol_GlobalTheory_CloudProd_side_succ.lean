-- Prove2me | solution 1 for GlobalTheory.CloudProd.side_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:21.975883+00:00
-- url     : https://prove2.me/submissions/7fa140c1-b86c-4d73-b5c1-55041c02cdfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SideSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CloudProd
namespace GlobalTheory.CloudProd
theorem _root_.solution (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n + 1 → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range (n + 1), (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by
  induction n with
  | zero =>
    have h1 : (1 + c) / max (δ 0) 1 ≤ 1 + c :=
      div_le_self (by linarith) (le_max_right _ _)
    simp only [zero_add, Finset.prod_range_one, Nat.cast_zero, mul_one]
    linarith
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have ih' := ih (fun j hj => h j (by omega))
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hd := h (m + 1) (by omega)
    push_cast at hd ⊢
    have hmax : (1 + c) * ((m : ℝ) + 1) ≤ max (δ (m + 1)) 1 := by
      refine le_trans ?_ (le_trans hd (le_max_left _ _))
      nlinarith
    have hpos : (0 : ℝ) < max (δ (m + 1)) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hf : (1 + c) / max (δ (m + 1)) 1 ≤ 1 / ((m : ℝ) + 1) := by
      rw [div_le_div_iff₀ hpos (by linarith)]
      linarith
    have hf0 : 0 ≤ 1 + (1 + c) / max (δ (m + 1)) 1 := by positivity
    calc _ ≤ ((2 + c) * ((m : ℝ) + 1)) * (1 + 1 / ((m : ℝ) + 1)) :=
          mul_le_mul ih' (by linarith) hf0 (by positivity)
      _ = (2 + c) * ((m : ℝ) + 1 + 1) := by field_simp
end GlobalTheory.CloudProd
