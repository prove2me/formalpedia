-- Prove2me | solution 1 for JRPHard.RangeDiv.nondivisor_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:15:43.200124+00:00
-- url     : https://prove2.me/submissions/dfac17d9-2e3d-4832-9790-dfc77693de0a

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting
open JRPHard.RangeDiv
set_option autoImplicit false

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, Lemma 3.
theorem solution (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) (q : ℕ)
    (hq : 0 < q) (hne : Nat.gcd q M ≠ q) :
    2 * Real.sqrt (2 * (L : ℝ) * U) ≤ obj5 M L U q ∧
      (L : ℝ) + U < obj5 M L U q := by
  have hg : 0 < Nat.gcd q M := Nat.gcd_pos_of_pos_left M hq
  have hgR : 0 < (Nat.gcd q M : ℝ) := by exact_mod_cast hg
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_left q M
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · simp at hk
      omega
    · simp at hk
      exact hne hk.symm
  have htwo : 2 * Nat.gcd q M ≤ q := by
    calc
      2 * Nat.gcd q M ≤ Nat.gcd q M * k := by nlinarith
      _ = q := hk.symm
  have htwoR : 2 * (Nat.gcd q M : ℝ) ≤ q := by exact_mod_cast htwo
  have hprod := mul_le_mul_of_nonneg_right htwoR hgR.le
  have hsqrt : Real.sqrt (2 * (L : ℝ) * U) ^ 2 = 2 * (L : ℝ) * U :=
    Real.sq_sqrt (by positivity)
  have hid : obj5 M L U q * (Nat.gcd q M : ℝ) =
      (L : ℝ) * U + q * (Nat.gcd q M : ℝ) := by
    simp only [obj5, add_mul, Nat.cast_mul, div_mul_cancel₀ _ (ne_of_gt hgR)]
  have hb : 2 * Real.sqrt (2 * (L : ℝ) * U) ≤ obj5 M L U q := by
    by_contra hn
    have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hgR
    nlinarith [sq_nonneg (2 * (Nat.gcd q M : ℝ) - Real.sqrt (2 * (L : ℝ) * U))]
  exact ⟨hb, lt_of_lt_of_le hI.2.2.2 hb⟩
