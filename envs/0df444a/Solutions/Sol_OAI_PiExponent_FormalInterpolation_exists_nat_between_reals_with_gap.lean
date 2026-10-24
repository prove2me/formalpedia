-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_nat_between_reals_with_gap
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:47:21.667183+00:00
-- url     : https://prove2.me/submissions/06cdc8db-bd84-47be-8dcf-e60f0617a406

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring

theorem solution
    {a b : ℝ} (ha : 0 ≤ a) (hab : a + 1 < b) :
    ∃ n : ℕ, a ≤ (n : ℝ) ∧ (n : ℝ) < b := by
  have hfloor : (Int.floor a : ℝ) ≤ a := Int.floor_le a
  have hstrict : a < (Int.floor a : ℝ) + 1 := Int.lt_floor_add_one a
  let m : ℤ := Int.floor a + 1
  have hm : 0 ≤ m := by
    dsimp [m]
    exact_mod_cast (lt_of_le_of_lt ha hstrict).le
  let n : ℕ := m.toNat
  have hcast : (n : ℝ) = (m : ℝ) := by
    dsimp [n]
    exact_mod_cast (Int.toNat_of_nonneg hm)
  have hvalue : (n : ℝ) = (Int.floor a : ℝ) + 1 := by
    rw [hcast]
    dsimp [m]
    push_cast
    ring
  refine ⟨n, ?_, ?_⟩
  · rw [hvalue]
    exact hstrict.le
  · rw [hvalue]
    exact lt_of_le_of_lt (by nlinarith [hfloor]) hab