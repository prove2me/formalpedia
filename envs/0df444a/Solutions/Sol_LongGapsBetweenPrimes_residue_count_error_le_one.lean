-- Prove2me | solution 1 for LongGapsBetweenPrimes.residue_count_error_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:07.083515+00:00
-- url     : https://prove2.me/submissions/b7de9713-b07a-418e-90da-ac46bf8d97e6

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {m a : ℕ} (ha : a < m) (T : ℕ) :
    |(∑ n ∈ Finset.range T, residueIndicator m a n) - (T : ℝ) / m| ≤ 1 := by
  have hlo : ((T / m : ℕ) : ℝ) ≤ (T : ℝ) / m := Nat.cast_div_le
  have hhi : (T : ℝ) / m < ((T / m : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using Nat.lt_floor_add_one ((T : ℝ) / m)
  have hcount := congrArg (fun n : ℕ => (n : ℝ))
    (Nat.count_modEq_card T (by omega : 0 < m) a)
  simp only [Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt ha,
    Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hcount
  simp only [residueIndicator, Finset.sum_boole]
  rw [hcount]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith
end LongGapsBetweenPrimes
