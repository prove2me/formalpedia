-- Prove2me | solution 1 for KnodelPrimeCordial_knodel_three_regular_side1_residue_card__p2m_165d50bc_4001_44b9_bb11_e1f7ef0e1992_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:23.887203+00:00
-- url     : https://prove2.me/submissions/1c2e76d5-d9ac-4ef6-8260-28840006ec54

import Mathlib
theorem KnodelPrimeCordial_knodel_three_regular_side1_residue_card__p2m_165d50bc_4001_44b9_bb11_e1f7ef0e1992_a1 (m : ℕ) (hm : 5 ≤ m) (j : Fin m) : ({j.val, (j.val + m - 1) % m, (j.val + m - 3) % m} : Finset ℕ).card = 3 := by
  have hj := j.isLt
  rcases Nat.lt_or_ge j.val 3 with h | h
  · interval_cases hv : j.val
    · have e1 : (0 + m - 1) % m = m - 1 := by
        rw [show 0 + m - 1 = m - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
      have e2 : (0 + m - 3) % m = m - 3 := by
        rw [show 0 + m - 3 = m - 3 by omega]; exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2]
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega)]
      simp
    · have e1 : (1 + m - 1) % m = 0 := by rw [show 1 + m - 1 = m by omega]; exact Nat.mod_self m
      have e2 : (1 + m - 3) % m = m - 2 := by
        rw [show 1 + m - 3 = m - 2 by omega]; exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2]
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega)]
      simp
    · have e1 : (2 + m - 1) % m = 1 := by
        rw [show 2 + m - 1 = 1 + m by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
      have e2 : (2 + m - 3) % m = m - 1 := by
        rw [show 2 + m - 3 = m - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2]
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega)]
      simp
  · have e1 : (j.val + m - 1) % m = j.val - 1 := by
      rw [show j.val + m - 1 = (j.val - 1) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have e2 : (j.val + m - 3) % m = j.val - 3 := by
      rw [show j.val + m - 3 = (j.val - 3) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2]
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega)]
    simp

theorem solution (m : ℕ) (hm : 5 ≤ m) (j : Fin m) : ({j.val, (j.val + m - 1) % m, (j.val + m - 3) % m} : Finset ℕ).card = 3 := by
  have hj := j.isLt
  rcases Nat.lt_or_ge j.val 3 with h | h
  · interval_cases hv : j.val
    · have e1 : (0 + m - 1) % m = m - 1 := by
        rw [show 0 + m - 1 = m - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
      have e2 : (0 + m - 3) % m = m - 3 := by
        rw [show 0 + m - 3 = m - 3 by omega]; exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2]
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega)]
      simp
    · have e1 : (1 + m - 1) % m = 0 := by rw [show 1 + m - 1 = m by omega]; exact Nat.mod_self m
      have e2 : (1 + m - 3) % m = m - 2 := by
        rw [show 1 + m - 3 = m - 2 by omega]; exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2]
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega)]
      simp
    · have e1 : (2 + m - 1) % m = 1 := by
        rw [show 2 + m - 1 = 1 + m by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
      have e2 : (2 + m - 3) % m = m - 1 := by
        rw [show 2 + m - 3 = m - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2]
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega)]
      simp
  · have e1 : (j.val + m - 1) % m = j.val - 1 := by
      rw [show j.val + m - 1 = (j.val - 1) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have e2 : (j.val + m - 3) % m = j.val - 3 := by
      rw [show j.val + m - 3 = (j.val - 3) + m by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2]
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega)]
    simp

