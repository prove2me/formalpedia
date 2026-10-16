-- Prove2me | solution 1 for JRPHard.RangeDiv.cheap_divisor_in_range
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:13:08.792681+00:00
-- url     : https://prove2.me/submissions/2bebff6d-c196-4357-b783-ac2d1209b577

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting

open JRPHard.RangeDiv
set_option autoImplicit false

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Existing mathematical result: Schulz and Telha, arXiv:2007.09045v1, Lemma 3.
theorem solution (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) (q : ℕ)
    (hq : 0 < q) (hle : obj5 M L U q ≤ (L : ℝ) + U) :
    q ∣ M ∧ L ≤ q ∧ q ≤ U := by
  rcases hI with ⟨hL, hLU, hUM, hgap⟩
  have hg : 0 < Nat.gcd q M := Nat.gcd_pos_of_pos_left M hq
  have hgR : 0 < (Nat.gcd q M : ℝ) := by exact_mod_cast hg
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hLUR : (L : ℝ) ≤ U := by exact_mod_cast hLU
  have hmul : (L : ℝ) * U + q * (Nat.gcd q M : ℝ) ≤
      ((L : ℝ) + U) * (Nat.gcd q M : ℝ) := by
    have hh : (L : ℝ) * U / (Nat.gcd q M : ℝ) ≤ (L : ℝ) + U - q := by
      simpa only [obj5, Nat.cast_mul] using (le_sub_iff_add_le.mpr hle)
    have hh' := (div_le_iff₀ hgR).mp hh
    nlinarith
  have hdiv : q ∣ M := by
    by_contra hn
    have hneq : Nat.gcd q M ≠ q := fun h => hn (Nat.gcd_eq_left_iff_dvd.mp h)
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left q M
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simp at hk
        omega
      · simp at hk
        exact hneq hk.symm
    have htwo : 2 * Nat.gcd q M ≤ q := by
      calc
        2 * Nat.gcd q M ≤ Nat.gcd q M * k := by nlinarith
        _ = q := hk.symm
    have htwoR : 2 * (Nat.gcd q M : ℝ) ≤ q := by exact_mod_cast htwo
    have hprod := mul_le_mul_of_nonneg_right htwoR hgR.le
    have hsqrt : Real.sqrt (2 * (L : ℝ) * U) ^ 2 = 2 * (L : ℝ) * U :=
      Real.sq_sqrt (by positivity)
    have hstrict := mul_lt_mul_of_pos_right hgap hgR
    nlinarith [sq_nonneg (2 * (Nat.gcd q M : ℝ) - Real.sqrt (2 * (L : ℝ) * U))]
  have hgq : Nat.gcd q M = q := Nat.gcd_eq_left_iff_dvd.mpr hdiv
  rw [hgq] at hmul
  refine ⟨hdiv, ?_, ?_⟩
  · by_contra hn
    have hlt : (q : ℝ) < L := by exact_mod_cast (lt_of_not_ge hn)
    have hpos := mul_pos (sub_pos.mpr hlt) (sub_pos.mpr (lt_of_lt_of_le hlt hLUR))
    nlinarith
  · by_contra hn
    have hlt : (U : ℝ) < q := by exact_mod_cast (lt_of_not_ge hn)
    have hpos := mul_pos (sub_pos.mpr (lt_of_le_of_lt hLUR hlt)) (sub_pos.mpr hlt)
    nlinarith
