-- Prove2me | solution 1 for KnodelPrimeCordial.offset_zero_index_wrap__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:23.108479+00:00
-- url     : https://prove2.me/submissions/dc947a90-10cc-4f10-8192-62718df4120f

import Mathlib
theorem KnodelPrimeCordial.offset_zero_index_wrap__p2m_6898b9ca_71f5_4ea4_932e_4d60ff156641_a1
    (n : ℕ) (hmod : n % 12 = 6) (j : Fin (n / 2)) (hj : j.val ≠ 0) :
    (2 * ((j.val + 2 ^ 0 - 1) % (n / 2)) + n - 1) % n =
      2 * j.val - 1 := by
  have hj2 := j.isLt
  have hn2 : 0 < n / 2 := by omega
  have e1 : (j.val + 2 ^ 0 - 1) % (n / 2) = j.val := by
    rw [pow_zero, Nat.add_sub_cancel]; exact Nat.mod_eq_of_lt hj2
  rw [e1]
  have e2 : 2 * j.val + n - 1 = (2 * j.val - 1) + n := by omega
  rw [e2, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem solution
    (n : ℕ) (hmod : n % 12 = 6) (j : Fin (n / 2)) (hj : j.val ≠ 0) :
    (2 * ((j.val + 2 ^ 0 - 1) % (n / 2)) + n - 1) % n =
      2 * j.val - 1 := by
  have hj2 := j.isLt
  have hn2 : 0 < n / 2 := by omega
  have e1 : (j.val + 2 ^ 0 - 1) % (n / 2) = j.val := by
    rw [pow_zero, Nat.add_sub_cancel]; exact Nat.mod_eq_of_lt hj2
  rw [e1]
  have e2 : 2 * j.val + n - 1 = (2 * j.val - 1) + n := by omega
  rw [e2, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

