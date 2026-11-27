-- Prove2me | solution 1 for LLMThroughput.TokenBudget.Supplement.lemma_24
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:29.229206+00:00
-- url     : https://prove2.me/submissions/f088dd70-5323-4743-8398-b6e7b00eafe1

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Supplement_BatchTime

open LLMThroughput
open LLMThroughput.TokenBudget
open LLMThroughput.TokenBudget.Supplement

theorem solution (a c b0 bmax : ℝ) (ha : 0 < a) (hc : 0 ≤ c)
    (hb0 : 0 < b0) (x y : ℕ) (hcap : (x : ℝ) + b0 ≤ bmax) :
    (x : ℝ) / batchTime a c b0 ((x : ℝ) + (y : ℝ)) ≤
      ((x : ℝ) + b0) / batchTime a c b0 ((x : ℝ) + (y : ℝ) + b0) := by
        have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
        have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg y
        have hceil : ((x : ℝ) + (y : ℝ)) / b0 ≤
            (⌈((x : ℝ) + (y : ℝ)) / b0⌉ : ℤ) := Int.le_ceil _
        have hk : (0 : ℝ) ≤ (⌈((x : ℝ) + (y : ℝ)) / b0⌉ : ℤ) :=
          le_trans (div_nonneg (add_nonneg hx hy) (le_of_lt hb0)) hceil
        have hshift : batchTime a c b0 ((x : ℝ) + (y : ℝ) + b0) =
            batchTime a c b0 ((x : ℝ) + (y : ℝ)) + a := by
          simp only [batchTime, add_div, div_self (ne_of_gt hb0), Int.ceil_add_one,
            Int.cast_add, Int.cast_one]
          ring
        have ht : 0 ≤ batchTime a c b0 ((x : ℝ) + (y : ℝ)) := by
          unfold batchTime
          exact add_nonneg hc (mul_nonneg (le_of_lt ha) hk)
        have ht' : 0 < batchTime a c b0 ((x : ℝ) + (y : ℝ) + b0) := by
          rw [hshift]
          linarith
        by_cases hx0 : x = 0
        · simpa only [hx0, Nat.cast_zero, zero_div, zero_add] using
            (div_nonneg (add_nonneg hx (le_of_lt hb0)) (le_of_lt ht'))
        · have hxp : (0 : ℝ) < x := by exact_mod_cast Nat.pos_of_ne_zero hx0
          have hkp : (0 : ℝ) < (⌈((x : ℝ) + (y : ℝ)) / b0⌉ : ℤ) :=
            lt_of_lt_of_le (div_pos (by linarith) hb0) hceil
          have htp : 0 < batchTime a c b0 ((x : ℝ) + (y : ℝ)) := by
            unfold batchTime
            exact add_pos_of_nonneg_of_pos hc (mul_pos ha hkp)
          apply (div_le_div_iff₀ htp ht').2
          rw [hshift]
          have hbound : (x : ℝ) + (y : ℝ) ≤
              (⌈((x : ℝ) + (y : ℝ)) / b0⌉ : ℤ) * b0 :=
            (div_le_iff₀ hb0).1 hceil
          unfold batchTime
          nlinarith [mul_nonneg (le_of_lt ha) (show 0 ≤
            (⌈((x : ℝ) + (y : ℝ)) / b0⌉ : ℤ) * b0 - x by linarith),
            mul_nonneg (le_of_lt hb0) hc]
