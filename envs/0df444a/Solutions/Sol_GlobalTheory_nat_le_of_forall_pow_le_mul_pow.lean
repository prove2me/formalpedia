-- Prove2me | solution 1 for GlobalTheory.nat_le_of_forall_pow_le_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:55.941143+00:00
-- url     : https://prove2.me/submissions/0a0aba15-b513-493a-8e70-0df600191c9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogConcaveMultiplicativeGrowthBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (x y C : ℕ) (h : ∀ j, x ^ j ≤ C * y ^ j) : x ≤ y := by
  by_contra hlt
  push_neg at hlt
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have := h 1
    simp at this
    omega
  · have hyR : (0:ℝ) < y := by exact_mod_cast hy
    have hq : (1:ℝ) < (x:ℝ) / y := by
      rw [one_lt_div hyR]; exact_mod_cast hlt
    obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (C:ℝ)).exists
    have h1 : ((x:ℝ))^j ≤ C * (y:ℝ)^j := by exact_mod_cast h j
    rw [div_pow, lt_div_iff₀ (pow_pos hyR j)] at hj
    linarith
end GlobalTheory
