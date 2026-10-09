-- Prove2me | solution 1 for Helfgott.centered_prime_finite_moment_twenty_one_billion
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:40:01.732693+00:00
-- url     : https://prove2.me/submissions/2a6d616b-9791-44ab-838f-feb29d46f684

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma elementary_log_le_sqrt (x : ℝ) (hx : 0 < x) : Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hh := Real.log_le_sub_one_of_pos (div_pos hs (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div hs.ne' (by norm_num), Real.log_sqrt hx.le] at hh
  have htwo : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  linarith

lemma elementary_psi_four (x : ℝ) (hx : 0 ≤ x) : Chebyshev.psi x ≤ 4 * x := by
  by_cases h1 : x < 1
  · rw [Chebyshev.psi_eq_zero_of_lt_two (by linarith)]
    positivity
  have h1' : 1 ≤ x := le_of_not_gt h1
  have hb := Chebyshev.psi_le h1'
  have hlog := elementary_log_le_sqrt x (by linarith)
  have hm := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
  have hsq := Real.sq_sqrt hx
  have hfour : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have hf := mul_le_mul_of_nonneg_right hfour hx
  nlinarith

lemma elementary_psi_nat_four (N : ℕ) :
    (∑ n ∈ Icc 1 N, vonMangoldt n) ≤ 4 * (N : ℝ) := by
  have he : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have hb := elementary_psi_four (N : ℝ) (by positivity)
  simpa only [Chebyshev.psi, Nat.floor_natCast, he] using hb

lemma elementary_prime_harmonic (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Icc 1 N, vonMangoldt n / (n : ℝ)) ≤ Real.log (N : ℝ) + 4 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hidentity : (∑ n ∈ Icc 1 N, Real.log (n : ℝ)) =
      ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) * vonMangoldt d := by
    have hi := finite_positive_divisor_reindex N (fun d _ => vonMangoldt d)
    simp only [vonMangoldt_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel_right,
      nsmul_eq_mul] at hi
    exact hi
  have hprod : (N : ℝ) * (∑ d ∈ Icc 1 N, vonMangoldt d / (d : ℝ)) ≤
      (∑ n ∈ Icc 1 N, Real.log (n : ℝ)) + (∑ d ∈ Icc 1 N, vonMangoldt d) := by
    rw [hidentity, ← sum_add_distrib, mul_sum]
    apply sum_le_sum
    intro d hd
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    have hh : (N : ℝ) ≤ (((N / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
      have hn := Nat.lt_mul_div_succ N hd0
      have hn' : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by exact_mod_cast hn
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hh (vonMangoldt_nonneg (n := d))
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hdr).mpr
    convert hm using 1 <;> ring
  have hlogs : (∑ n ∈ Icc 1 N, Real.log (n : ℝ)) ≤ (N : ℝ) * Real.log (N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, Real.log (N : ℝ) := by
        apply sum_le_sum
        intro n hn
        exact Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1)
          (by exact_mod_cast (mem_Icc.mp hn).2)
      _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel_right, nsmul_eq_mul]
  apply (mul_le_mul_iff_right₀ hNr).mp
  have hp := elementary_psi_nat_four N
  nlinarith


lemma elementary_harmonic (N : ℕ) :
    (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) ≤ Real.log (N : ℝ) + 1 := by
  have hh := harmonic_le_one_add_log N
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    one_div, add_comm] using hh

lemma elementary_prime_convolution_nonneg (n : ℕ) :
    0 ≤ (vonMangoldt * vonMangoldt) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg (fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)

lemma elementary_prime_convolution_reindex (N : ℕ) :
    (∑ n ∈ Icc 1 N, (vonMangoldt * vonMangoldt) n) =
      ∑ d ∈ Icc 1 N, vonMangoldt d * (∑ r ∈ Icc 1 (N / d), vonMangoldt r) := by
  have hp (n : ℕ) : (vonMangoldt * vonMangoldt) n =
      ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d) := by
    rw [ArithmeticFunction.mul_apply]
    exact Nat.sum_divisorsAntidiagonal (fun d r : ℕ => vonMangoldt d * vonMangoldt r)
  simp_rw [hp]
  rw [finite_positive_divisor_reindex N (fun d r => vonMangoldt d * vonMangoldt r)]
  simp_rw [← mul_sum]

lemma elementary_prime_convolution_harmonic_reindex (N : ℕ) :
    (∑ n ∈ Icc 1 N, (vonMangoldt * vonMangoldt) n / (n : ℝ)) =
      ∑ d ∈ Icc 1 N, (vonMangoldt d / (d : ℝ)) *
        (∑ r ∈ Icc 1 (N / d), vonMangoldt r / (r : ℝ)) := by
  have hp (n : ℕ) : (vonMangoldt * vonMangoldt) n =
      ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d) := by
    rw [ArithmeticFunction.mul_apply]
    exact Nat.sum_divisorsAntidiagonal (fun d r : ℕ => vonMangoldt d * vonMangoldt r)
  have he : (∑ n ∈ Icc 1 N, (vonMangoldt * vonMangoldt) n / (n : ℝ)) =
      ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors,
        (vonMangoldt d / (d : ℝ)) * (vonMangoldt (n / d) / ((n / d : ℕ) : ℝ)) := by
    apply sum_congr rfl
    intro n hn
    rw [hp, sum_div]
    apply sum_congr rfl
    intro d hd
    have hn0 : 0 < n := (mem_Icc.mp hn).1
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn0
    have hr0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn0 hdvd) hd0
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    have hrr : (0 : ℝ) < (n / d : ℕ) := by exact_mod_cast hr0
    have hprod : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
    rw [hprod]
    field_simp
  rw [he, finite_positive_divisor_reindex N
    (fun d r => (vonMangoldt d / (d : ℝ)) * (vonMangoldt r / (r : ℝ)))]
  simp_rw [← mul_sum]

lemma elementary_prime_combined_harmonic_bound (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Icc 1 N, (vonMangoldt * vonMangoldt) n / (n : ℝ)) +
      (∑ n ∈ Icc 1 N, vonMangoldt n * Real.log (n : ℝ) / (n : ℝ)) ≤
        (Real.log (N : ℝ) + 4) ^ 2 := by
  let S : ℝ := ∑ n ∈ Icc 1 N, vonMangoldt n / (n : ℝ)
  let G : ℝ := ∑ n ∈ Icc 1 N, vonMangoldt n * Real.log (n : ℝ) / (n : ℝ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hS : S ≤ Real.log (N : ℝ) + 4 := elementary_prime_harmonic N hN
  have hmain : (∑ n ∈ Icc 1 N, (vonMangoldt * vonMangoldt) n / (n : ℝ)) ≤
      (Real.log (N : ℝ) + 4) * S - G := by
    rw [elementary_prime_convolution_harmonic_reindex]
    calc
      _ ≤ ∑ d ∈ Icc 1 N, (vonMangoldt d / (d : ℝ)) *
          (Real.log (N : ℝ) - Real.log (d : ℝ) + 4) := by
        apply sum_le_sum
        intro d hd
        have hd0 : 0 < d := (mem_Icc.mp hd).1
        have hdN : d ≤ N := (mem_Icc.mp hd).2
        have hq : 0 < N / d := Nat.div_pos hdN hd0
        have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
        have hqr : (0 : ℝ) < (N / d : ℕ) := by exact_mod_cast hq
        have hf : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
          apply (le_div_iff₀ hdr).mpr
          exact_mod_cast Nat.div_mul_le_self N d
        have hl := Real.log_le_log hqr hf
        rw [Real.log_div hNr.ne' hdr.ne'] at hl
        have hb := elementary_prime_harmonic (N / d) hq
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by
        dsimp only [S, G]
        rw [mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro d _
        ring
  change _ + G ≤ _
  have hm := mul_le_mul_of_nonneg_left hS (by linarith : 0 ≤ Real.log (N : ℝ) + 4)
  nlinarith

lemma elementary_prime_convolution_sum_bound (N : ℕ) :
    (∑ n ∈ Icc 1 N, (vonMangoldt * vonMangoldt) n) ≤
      4 * (N : ℝ) * (∑ d ∈ Icc 1 N, vonMangoldt d / (d : ℝ)) := by
  rw [elementary_prime_convolution_reindex, mul_sum]
  apply sum_le_sum
  intro d hd
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  have hf : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    apply (le_div_iff₀ hdr).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  have hb := elementary_psi_nat_four (N / d)
  have hh : (∑ r ∈ Icc 1 (N / d), vonMangoldt r) ≤ 4 * ((N : ℝ) / (d : ℝ)) := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hh (vonMangoldt_nonneg (n := d))
  convert hm using 1 <;> ring

lemma elementary_prime_log_sum_bound (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Icc 1 N, vonMangoldt n * Real.log (n : ℝ)) ≤
      4 * (N : ℝ) * Real.log (N : ℝ) := by
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, vonMangoldt n * Real.log (N : ℝ) := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1)
          (by exact_mod_cast (mem_Icc.mp hn).2)) vonMangoldt_nonneg
    _ = (∑ n ∈ Icc 1 N, vonMangoldt n) * Real.log (N : ℝ) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (elementary_psi_nat_four N) hlog0


lemma elementary_centered_prime_coefficient_abs (n : ℕ) (C : ℝ)
    (hn : 1 ≤ n) (hC : |C| ≤ 2) :
    |(vonMangoldt * vonMangoldt) n - vonMangoldt n * Real.log (n : ℝ) + C| ≤
      (vonMangoldt * vonMangoldt) n + vonMangoldt n * Real.log (n : ℝ) + 2 := by
  have hc := elementary_prime_convolution_nonneg n
  have hg : 0 ≤ vonMangoldt n * Real.log (n : ℝ) :=
    mul_nonneg vonMangoldt_nonneg (Real.log_nonneg (by exact_mod_cast hn))
  have hs := abs_sub ((vonMangoldt * vonMangoldt) n) (vonMangoldt n * Real.log (n : ℝ))
  rw [abs_of_nonneg hc, abs_of_nonneg hg] at hs
  have ha := abs_add_le
    ((vonMangoldt * vonMangoldt) n - vonMangoldt n * Real.log (n : ℝ)) C
  linarith

theorem centered_prime_finite_moment_elementary_bound (K : ℕ) (C : ℝ)
    (hK : 0 < K) (hC : |C| ≤ 2) :
    ((∑ k ∈ Icc 1 K,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 K,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (K : ℝ)) ≤ Real.log (K : ℝ) ^ 2 + 18 * Real.log (K : ℝ) + 36 := by
  let S : ℝ := ∑ n ∈ Icc 1 K, vonMangoldt n / (n : ℝ)
  let H : ℝ := ∑ n ∈ Icc 1 K, 1 / (n : ℝ)
  let P : ℝ := ∑ n ∈ Icc 1 K, (vonMangoldt * vonMangoldt) n / (n : ℝ)
  let G : ℝ := ∑ n ∈ Icc 1 K, vonMangoldt n * Real.log (n : ℝ) / (n : ℝ)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
  have hS : S ≤ Real.log (K : ℝ) + 4 := elementary_prime_harmonic K hK
  have hH : H ≤ Real.log (K : ℝ) + 1 := elementary_harmonic K
  have hPG : P + G ≤ (Real.log (K : ℝ) + 4) ^ 2 :=
    elementary_prime_combined_harmonic_bound K hK
  have hweighted : (∑ k ∈ Icc 1 K,
      |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
        (k : ℝ)) ≤ P + G + 2 * H := by
    calc
      _ ≤ ∑ k ∈ Icc 1 K,
          ((vonMangoldt * vonMangoldt) k + vonMangoldt k * Real.log (k : ℝ) + 2) /
            (k : ℝ) := by
        apply sum_le_sum
        intro k hk
        exact div_le_div_of_nonneg_right
          (elementary_centered_prime_coefficient_abs k C (mem_Icc.mp hk).1 hC)
          (by positivity)
      _ = _ := by
        dsimp only [P, G, H]
        simp_rw [add_div]
        rw [sum_add_distrib, sum_add_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro k _
        ring
  have hplain : |∑ k ∈ Icc 1 K,
      ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
      (∑ k ∈ Icc 1 K, (vonMangoldt * vonMangoldt) k) +
        (∑ k ∈ Icc 1 K, vonMangoldt k * Real.log (k : ℝ)) + 2 * (K : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Icc 1 K,
          |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 K,
          ((vonMangoldt * vonMangoldt) k + vonMangoldt k * Real.log (k : ℝ) + 2) :=
        sum_le_sum (fun k hk => elementary_centered_prime_coefficient_abs k C (mem_Icc.mp hk).1 hC)
      _ = _ := by
        simp only [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel_right, nsmul_eq_mul]
        ring
  have hPplain : (∑ k ∈ Icc 1 K, (vonMangoldt * vonMangoldt) k) ≤ 4 * (K : ℝ) * S :=
    elementary_prime_convolution_sum_bound K
  have hGplain := elementary_prime_log_sum_bound K hK
  have hquotient : |∑ k ∈ Icc 1 K,
      ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
        (K : ℝ) ≤ 4 * S + 4 * Real.log (K : ℝ) + 2 := by
    apply (div_le_iff₀ hKr).mpr
    nlinarith
  nlinarith

lemma elementary_moment_cutoff_log_upper : Real.log (21000000000 : ℝ) ≤ 24 := by
  have hb := Real.log_le_log (by norm_num : (0 : ℝ) < 21000000000)
    (by norm_num : (21000000000 : ℝ) ≤ 5 * 2 ^ (32 : ℕ))
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at hb
  norm_num only [Nat.cast_ofNat] at hb
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem centered_prime_finite_moment_twenty_one_billion_complete (C : ℝ) (hC : |C| ≤ 2) :
    ((∑ k ∈ Icc 1 21000000000,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 21000000000,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (21000000000 : ℝ)) ≤ 4345 / 4 := by
  have hb := centered_prime_finite_moment_elementary_bound 21000000000 C (by norm_num) hC
  have hl := elementary_moment_cutoff_log_upper
  have h0 : 0 ≤ Real.log (21000000000 : ℝ) := Real.log_nonneg (by norm_num)
  have hs := pow_le_pow_left₀ h0 hl 2
  norm_num only [Nat.cast_ofNat] at hb
  nlinarith

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution  (C : ℝ) (hC : |C| ≤ 2) :
    ((∑ k ∈ Icc 1 21000000000,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 21000000000,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (21000000000 : ℝ)) ≤ 4345 / 4 := Helfgott.centered_prime_finite_moment_twenty_one_billion_complete C hC
#print axioms solution
