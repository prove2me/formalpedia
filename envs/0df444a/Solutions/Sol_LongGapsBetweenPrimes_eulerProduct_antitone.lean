-- Prove2me | solution 1 for LongGapsBetweenPrimes.eulerProduct_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:45.197812+00:00
-- url     : https://prove2.me/submissions/ba105de6-ed74-42ea-9f16-ac8418b06175

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (N : ℕ) {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ ≤ τ) :
    eulerProduct N τ ≤ eulerProduct N σ := by
  apply Finset.prod_le_prod
  · intro p hp
    exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)).le)
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    have hden : 0 < 1 - (p : ℝ) ^ (-σ) :=
      sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le hden
    have h := Real.rpow_le_rpow_of_exponent_le hp1.le (show -τ ≤ -σ by linarith)
    linarith
end LongGapsBetweenPrimes
