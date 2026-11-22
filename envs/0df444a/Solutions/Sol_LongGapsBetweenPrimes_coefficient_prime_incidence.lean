-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficient_prime_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:55:37.353791+00:00
-- url     : https://prove2.me/submissions/d0b64116-678f-436f-88c6-df67c60c483a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_divisors_dvd_eq
import Theorems.Thm_LongGapsBetweenPrimes_abs_coefficient_mul_le
import Theorems.Thm_LongGapsBetweenPrimes_sum_abs_coefficient_div_totient

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P p : ℕ} (hP : 1 < P) (hsq : Squarefree P)
    (hp : p.Prime) (hpP : p ∣ P) (hcoeff : |coefficient P p| ≤ 1) :
    (∑ d ∈ P.divisors.filter (fun d => p ∣ d), |coefficient P d| / d.totient) ≤
      4 / (p : ℝ) := by
  have hP0 : P ≠ 0 := by omega
  have hpR : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  rw [sum_divisors_dvd_eq hP0 hp.pos hpP]
  calc
    _ ≤ ∑ e ∈ (P / p).divisors,
        (|coefficient P e| / e.totient) / ((p : ℝ) - 1) := by
      apply Finset.sum_le_sum
      intro e he
      have hcop : p.Coprime e := by
        apply hp.coprime_iff_not_dvd.mpr
        intro hpe
        have hpeP := (Nat.dvd_div_iff_mul_dvd hpP).mp (Nat.dvd_of_mem_divisors he)
        exact hp.ne_one (Nat.isUnit_iff.mp (hsq p ((mul_dvd_mul_left p hpe).trans hpeP)))
      have hcoeff' : |coefficient P (p * e)| ≤ |coefficient P e| := by
        by_cases he1 : e = 1
        · simpa [he1, coefficient] using hcoeff
        · exact abs_coefficient_mul_le hP hp.one_le
            (by have := Nat.pos_of_mem_divisors he; omega)
      rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul,
        Nat.cast_sub hp.one_le, Nat.cast_one]
      calc
        _ ≤ |coefficient P e| / (((p : ℝ) - 1) * e.totient) :=
          div_le_div_of_nonneg_right hcoeff' (mul_nonneg hpR.le (Nat.cast_nonneg _))
        _ = _ := by rw [mul_comm, div_mul_eq_div_div]
    _ = (∑ e ∈ (P / p).divisors, |coefficient P e| / e.totient) /
        ((p : ℝ) - 1) := by rw [Finset.sum_div]
    _ ≤ 2 / ((p : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right _ hpR.le
      calc
        _ ≤ ∑ e ∈ P.divisors, |coefficient P e| / e.totient :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Nat.divisors_subset_of_dvd hP0 (Nat.div_dvd_of_dvd hpP))
            (fun _ _ _ => by positivity)
        _ = 2 := sum_abs_coefficient_div_totient hP
    _ ≤ 4 / (p : ℝ) := by
      apply (div_le_div_iff₀ hpR (by exact_mod_cast hp.pos)).mpr
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
end LongGapsBetweenPrimes
