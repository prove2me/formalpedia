-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.choose_weighted_row_le_four_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T09:12:03.891659+00:00
-- url     : https://prove2.me/submissions/2065c6e7-2659-4a22-9120-3c242407f06e

import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (a b : ℕ) :
    a.choose b * 3 ^ (a - b) ≤ 4 ^ a := by
  have pow_bound (n : ℕ) : 3 ^ n ≤ 4 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        calc
          3 ^ n * 3 ≤ 4 ^ n * 3 := Nat.mul_le_mul_right 3 ih
          _ ≤ 4 ^ n * 4 := Nat.mul_le_mul_left (4 ^ n) (by omega)
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => simp
      | succ b => simp
  | succ a ih =>
      cases b with
      | zero =>
          simpa [Nat.choose_zero_right] using pow_bound (a + 1)
      | succ b =>
          by_cases hb : b < a
          · have hpascal := Nat.choose_succ_succ a b
            have hexp : a - b = a - (b + 1) + 1 := by omega
            have hpow : 3 ^ (a - b) = 3 ^ (a - (b + 1)) * 3 := by
              rw [hexp, pow_succ]
            rw [Nat.choose_succ_succ]
            have hsub : a + 1 - (b + 1) = a - b := by omega
            rw [hsub]
            calc
              (a.choose b + a.choose (b + 1)) * 3 ^ (a - b) =
                  a.choose b * 3 ^ (a - b) +
                    a.choose (b + 1) * 3 ^ (a - b) := by ring
              _ = a.choose b * 3 ^ (a - b) +
                    3 * (a.choose (b + 1) * 3 ^ (a - (b + 1))) := by
                    rw [hpow]
                    ring
              _ ≤ 4 ^ a + 3 * 4 ^ a := by
                    exact add_le_add (ih b)
                      (Nat.mul_le_mul_left 3 (ih (b + 1)))
              _ = 4 ^ (a + 1) := by rw [pow_succ]; ring
          · by_cases heq : b = a
            · subst b
              simp
              have hpos : 0 < 4 ^ (a + 1) := by positivity
              omega
            · have hchoose : (a + 1).choose (b + 1) = 0 := by
                apply Nat.choose_eq_zero_of_lt
                omega
              rw [hchoose]
              simp