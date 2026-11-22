-- Prove2me | solution 1 for MasulloRH.prime_resolvent_zero_profile_and_uniform_prime_power_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:45:40.329124+00:00
-- url     : https://prove2.me/submissions/51a5eb50-640e-42c4-8d33-8ebb6d4c336f

import Mathlib
import Theorems.Thm_Zeta23_Cheb_defect_bounded_explicit
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_sq_div_eq_explicit

open Finset Real
open ArithmeticFunction hiding log

theorem solution (x : ℝ) (hx : 2 ≤ x) :
    (|(∑ n ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log n ^ 2 / n) -
       Real.log x ^ 2 / 2| ≤
       (2 * (Real.log 4 + 4) + 1537 / Real.log 2) * Real.log x + 1537) ∧
    (∀ w : ℕ → ℂ, (∀ n, ‖w n‖ ≤ 1) →
      ‖(∑ n ∈ Ioc 0 ⌊x⌋₊, w n * ((Λ n ^ 2 / n : ℝ) : ℂ)) -
        ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime,
          w n * ((Real.log n ^ 2 / n : ℝ) : ℂ)‖ ≤ 1537) := by
  classical
  let S := Ioc 0 ⌊x⌋₊
  let A (n : ℕ) : ℝ := Λ n ^ 2 / n
  let B (n : ℕ) : ℝ := if n.Prime then Real.log n ^ 2 / n else 0
  have gap (n : ℕ) : 0 ≤ A n - B n ∧
      A n - B n ≤ Λ n * (Real.log n - Λ n) / n := by
    by_cases hp : n.Prime
    · simp [A, B, hp, vonMangoldt_apply_prime hp]
    by_cases hpow : IsPrimePow n
    · obtain ⟨p, k, hprime, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
      have hk1 : k ≠ 1 := by rintro rfl; simp_all
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
      simp only [A, B, if_neg hp, sub_zero, vonMangoldt_apply_pow hk.ne',
        vonMangoldt_apply_prime hprime, Nat.cast_pow, Real.log_pow]
      constructor
      · positivity
      · apply div_le_div_of_nonneg_right _ (by positivity)
        have h := mul_le_mul_of_nonneg_right hk2 hl
        nlinarith [mul_nonneg hl (show 0 ≤ (k:ℝ)*Real.log p - 2*Real.log p by linarith)]
    · simp [A, B, hp, vonMangoldt_eq_zero_iff.mpr hpow]
  have bound : (∑ n ∈ S, (A n - B n)) ≤ 1537 :=
    (sum_le_sum (fun n _ => (gap n).2)).trans (Zeta23.Cheb.defect_bounded_explicit x)
  have nonneg : 0 ≤ ∑ n ∈ S, (A n - B n) := sum_nonneg fun n _ => (gap n).1
  have hsum : (∑ n ∈ S, B n) = ∑ n ∈ S.filter Nat.Prime, Real.log n ^ 2 / n := by
    simp [B, sum_filter]
  constructor
  · change |(∑ n ∈ S.filter Nat.Prime, _) - _| ≤ _
    rw [← hsum]
    have hfull := Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit x hx
    change |(∑ n ∈ S, A n) - _| ≤ _ at hfull
    rw [abs_le] at hfull ⊢
    rw [sum_sub_distrib] at bound nonneg
    constructor <;> linarith [hfull.1, hfull.2]
  · intro w hw
    have hf : (∑ n ∈ S.filter Nat.Prime, w n * ((Real.log n ^ 2 / n : ℝ) : ℂ)) =
        ∑ n ∈ S, w n * (B n : ℂ) := by
      rw [sum_filter]
      exact sum_congr rfl fun n _ => by by_cases h : n.Prime <;> simp [B, h]
    change ‖(∑ n ∈ S, w n * (A n : ℂ)) - _‖ ≤ _
    rw [hf, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((sum_le_sum (fun n _ => ?_)).trans bound)
    rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (gap n).1]
    simpa using mul_le_mul_of_nonneg_right (hw n) (gap n).1
