-- Prove2me | solution 1 for LongGapsBetweenPrimes.eulerProduct_ge_power_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:59.471502+00:00
-- url     : https://prove2.me/submissions/8773ed3b-9287-495b-8d60-99ec4f9724e1

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_smooth_le_eulerProduct

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (Y : ℕ) {t : ℝ} (ht : 0 < t) :
    (1 - ((Y : ℝ) + 1) ^ (-t)) / t ≤ eulerProduct Y (1 + t) := by
  calc
    _ = ∫ x : ℝ in 1..(Y : ℝ) + 1, x ^ (-(1 + t)) := by
      rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
      · rw [show -(1 + t) + 1 = -t by ring, Real.one_rpow]
        ring
      · rw [Set.uIcc_of_le (le_add_of_nonneg_left (Nat.cast_nonneg Y))]
        norm_num
    _ ≤ ∑ n ∈ Finset.Ico 1 (Y + 1), (n : ℝ) ^ (-(1 + t)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        AntitoneOn.integral_le_sum_Ico (a := 1) (b := Y + 1)
          (f := fun x : ℝ => x ^ (-(1 + t))) (by omega) (by
            intro x hx y _ hxy
            exact Real.rpow_le_rpow_of_nonpos
              (lt_of_lt_of_le (by norm_num) hx.1) hxy (by linarith))
    _ ≤ _ := sum_smooth_le_eulerProduct (by linarith)
      (Finset.Ico 1 (Y + 1)) (fun n hn => Nat.mem_smoothNumbers_of_lt
        (by have := Finset.mem_Ico.mp hn; omega) (Finset.mem_Ico.mp hn).2)
end LongGapsBetweenPrimes
