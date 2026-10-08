-- Prove2me | solution 1 for GoldieRenewal.Kesten.inequalities_9_26_9_27
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:43:44.305465+00:00
-- url     : https://prove2.me/submissions/a4cf935f-4fbe-473b-842b-c016c5cdd095

import Mathlib

private lemma small_power (a b r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    abs (a ^ r - b ^ r) ≤ abs (a - b) ^ r := by
  wlog hab : b ≤ a generalizing a b
  · simpa [abs_sub_comm] using this b a hb ha (le_of_not_ge hab)
  have hadd := Real.rpow_add_le_add_rpow hb (sub_nonneg.mpr hab) hr.le hr1
  rw [add_sub_cancel] at hadd
  rw [abs_of_nonneg (sub_nonneg.mpr hab),
    abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hb hab hr.le))]
  linarith

private lemma large_power (a b r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 1 < r) :
    abs (a ^ r - b ^ r) ≤ r * abs (a - b) * (max a b) ^ (r - 1) := by
  wlog hab : b ≤ a generalizing a b
  · simpa [abs_sub_comm, max_comm] using this b a hb ha (le_of_not_ge hab)
  rcases eq_or_lt_of_le hab with h | h
  · subst a
    simp
  have hs := (convexOn_rpow hr.le).slope_le_of_hasDerivAt hb ha h
    (Real.hasDerivAt_rpow_const (Or.inr hr.le))
  rw [slope_def_field] at hs
  have hd := (div_le_iff₀ (sub_pos.mpr h)).mp hs
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hb hab (by linarith))),
    abs_of_nonneg (sub_nonneg.mpr hab), max_eq_left hab]
  nlinarith

theorem solution :
    (∀ x y r : ℝ, 0 < r → |x + y| ^ r ≤ max ((2 : ℝ) ^ (r - 1)) 1 * (|x| ^ r + |y| ^ r)) ∧
    (∀ x y r : ℝ, 0 < r → r ≤ 1 → abs (|x| ^ r - |y| ^ r) ≤ |x - y| ^ r) ∧
    (∀ x y r : ℝ, 1 < r → abs (|x| ^ r - |y| ^ r) ≤ r * |x - y| * (max |x| |y|) ^ (r - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y r hr
    have ht := Real.rpow_le_rpow (abs_nonneg (x+y)) (abs_add_le x y) hr.le
    by_cases h : r ≤ 1
    · have hh := Real.rpow_add_le_add_rpow (abs_nonneg x) (abs_nonneg y) hr.le h
      have hs : 0 ≤ |x| ^ r + |y| ^ r := by positivity
      exact ht.trans (hh.trans (by nlinarith [le_max_right ((2:ℝ)^(r-1)) 1]))
    · have hh : (|x| + |y|) ^ r ≤ (2 : ℝ) ^ (r - 1) * (|x| ^ r + |y| ^ r) := by
        exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
          (⟨|x|, abs_nonneg x⟩ : NNReal) (⟨|y|, abs_nonneg y⟩ : NNReal) (le_of_not_ge h)
      have hs : 0 ≤ |x| ^ r + |y| ^ r := by positivity
      exact ht.trans (hh.trans (by nlinarith [le_max_left ((2:ℝ)^(r-1)) 1]))
  · intro x y r hr hr1
    exact (small_power |x| |y| r (abs_nonneg x) (abs_nonneg y) hr hr1).trans
      (Real.rpow_le_rpow (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub x y) hr.le)
  · intro x y r hr
    have hh := large_power |x| |y| r (abs_nonneg x) (abs_nonneg y) hr
    have hm := mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub x y)
      (show 0 ≤ r * (max |x| |y|) ^ (r - 1) by positivity)
    nlinarith

#print axioms solution
