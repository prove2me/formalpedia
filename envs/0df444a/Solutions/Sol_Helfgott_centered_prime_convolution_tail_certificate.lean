-- Prove2me | solution 1 for Helfgott.centered_prime_convolution_tail_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:02:03.031534+00:00
-- url     : https://prove2.me/submissions/4a97b6b5-2581-4f8b-9af8-8219655e0d92

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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
open Finset Nat
open scoped BigOperators Classical
namespace Helfgott

lemma sum_Icc_split_at (N H : ℕ) (hH : H ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, f n) =
      (∑ n ∈ Icc 1 H, f n) + ∑ n ∈ Ioc H N, f n := by
  have hd : Disjoint (Icc 1 H) (Ioc H N) := by
    rw [Finset.disjoint_left]
    intro n hn hm
    have hh := (mem_Icc.mp hn).2
    have hl := (mem_Ioc.mp hm).1
    omega
  have hu : Icc 1 H ∪ Ioc H N = Icc 1 N := by
    ext n
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  rw [← hu, sum_union hd]

theorem finite_hyperbola_tail_reindex (N K : ℕ) (hK : 0 < K)
    (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ Ioc (N / K) N, ∑ k ∈ Icc 1 (N / d), F d k) =
      ∑ k ∈ Icc 1 K, ∑ d ∈ Ioc (N / K) (N / k), F d k := by
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 i.1)]
  refine sum_bij (fun i _ => (⟨i.2, i.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hd, hk⟩
    have hdpos : 0 < i.1 := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hd).1
    have hkpos : 0 < i.2 := (mem_Icc.mp hk).1
    have hprod : i.2 * i.1 ≤ N :=
      (Nat.le_div_iff_mul_le hdpos).mp (mem_Icc.mp hk).2
    have hKprod : N < i.1 * K :=
      (Nat.div_lt_iff_lt_mul hK).mp (mem_Ioc.mp hd).1
    have hkK : i.2 ≤ K := by
      by_contra h
      have hle : K ≤ i.2 := by omega
      have hm := Nat.mul_le_mul_left i.1 hle
      nlinarith
    apply mem_sigma.mpr
    exact ⟨mem_Icc.mpr ⟨hkpos, hkK⟩,
      mem_Ioc.mpr ⟨(mem_Ioc.mp hd).1,
        (Nat.le_div_iff_mul_le hkpos).mpr (by simpa only [mul_comm] using hprod)⟩⟩
  · intro i hi j hj he
    have hd : i.1 = j.1 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hk : i.2 = j.2 := congrArg Sigma.fst he
    exact Sigma.ext hd (by simpa using hk)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hk, hd⟩
    have hkpos : 0 < j.1 := (mem_Icc.mp hk).1
    have hdpos : 0 < j.2 := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hd).1
    have hprod : j.2 * j.1 ≤ N :=
      (Nat.le_div_iff_mul_le hkpos).mp (mem_Ioc.mp hd).2
    have hdN : j.2 ≤ N := by nlinarith
    refine ⟨⟨j.2, j.1⟩, mem_sigma.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hd).1, hdN⟩,
      mem_Icc.mpr ⟨hkpos,
        (Nat.le_div_iff_mul_le hdpos).mpr (by simpa only [mul_comm] using hprod)⟩⟩, ?_⟩
    rfl
  · intro i hi
    rfl

theorem finite_dirichlet_hyperbola (N K : ℕ) (hK : 0 < K)
    (f g : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, f d * ∑ k ∈ Icc 1 (N / d), g k) =
      (∑ d ∈ Icc 1 (N / K), f d * ∑ k ∈ Icc 1 (N / d), g k) +
      (∑ k ∈ Icc 1 K, g k * ∑ d ∈ Icc 1 (N / k), f d) -
      (∑ d ∈ Icc 1 (N / K), f d) * (∑ k ∈ Icc 1 K, g k) := by
  rw [sum_Icc_split_at N (N / K) (Nat.div_le_self N K)]
  have htail :
      (∑ d ∈ Ioc (N / K) N, f d * ∑ k ∈ Icc 1 (N / d), g k) =
      (∑ k ∈ Icc 1 K, g k * ∑ d ∈ Icc 1 (N / k), f d) -
      (∑ d ∈ Icc 1 (N / K), f d) * (∑ k ∈ Icc 1 K, g k) := by
    conv_lhs => simp only [Finset.mul_sum]
    rw [finite_hyperbola_tail_reindex N K hK (fun d k => f d * g k)]
    have he (k : ℕ) (hk : k ∈ Icc 1 K) :
        (∑ d ∈ Ioc (N / K) (N / k), f d * g k) =
        g k * (∑ d ∈ Icc 1 (N / k), f d) -
          (∑ d ∈ Icc 1 (N / K), f d) * g k := by
      have hsmall : N / K ≤ N / k :=
        Nat.div_le_div_left (mem_Icc.mp hk).2 (mem_Icc.mp hk).1
      have hs := sum_Icc_split_at (N / k) (N / K) hsmall f
      rw [← Finset.sum_mul]
      rw [hs]
      ring
    rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [htail]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma finite_symmetric_dirichlet_hyperbola (N K : ℕ)
    (hK : 0 < K) (hlo : K * K ≤ N) (hhi : N < (K + 1) * (K + 1))
    (f : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, f d * ∑ k ∈ Icc 1 (N / d), f k) =
      2 * (∑ d ∈ Icc 1 K, f d * ∑ k ∈ Icc 1 (N / d), f k) -
        (∑ d ∈ Icc 1 K, f d) ^ 2 := by
  have hKH : K ≤ N / K := (Nat.le_div_iff_mul_le hK).mpr hlo
  have hHN : N / K ≤ N := Nat.div_le_self N K
  have hfixed (d : ℕ) (hd : d ∈ Ioc K (N / K)) : N / d = K := by
    have hd0 : 0 < d := by have := (mem_Ioc.mp hd).1; omega
    have hl : K ≤ N / d := (Nat.le_div_iff_mul_le hd0).mpr (by
      have ht := (Nat.le_div_iff_mul_le hK).mp (mem_Ioc.mp hd).2
      simpa only [mul_comm] using ht)
    have hh : N / d < K + 1 := (Nat.div_lt_iff_lt_mul hd0).mpr (by
      have hdK : K + 1 ≤ d := (mem_Ioc.mp hd).1
      exact hhi.trans_le (Nat.mul_le_mul_left (K + 1) hdK))
    omega
  have hleft : (∑ d ∈ Icc 1 (N / K), f d * ∑ k ∈ Icc 1 (N / d), f k) =
      (∑ d ∈ Icc 1 K, f d * ∑ k ∈ Icc 1 (N / d), f k) +
        (∑ d ∈ Ioc K (N / K), f d) * (∑ k ∈ Icc 1 K, f k) := by
    rw [sum_Icc_split_at (N / K) K hKH]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hfixed d hd]
  have htotal := finite_dirichlet_hyperbola N K hK f f
  rw [hleft, sum_Icc_split_at (N / K) K hKH] at htotal
  nlinarith [htotal]

lemma prime_psi_eq_sum_positive (x : ℝ) :
    Chebyshev.psi x = ∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n := by
  have he : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [Chebyshev.psi, he]

lemma prime_psi_nat (N : ℕ) :
    (∑ n ∈ Icc 1 N, vonMangoldt n) = Chebyshev.psi (N : ℝ) := by
  rw [prime_psi_eq_sum_positive, Nat.floor_natCast]

lemma prime_psi_ratio (N d : ℕ) :
    Chebyshev.psi ((N / d : ℕ) : ℝ) =
      Chebyshev.psi ((N : ℝ) / (d : ℝ)) := by
  rw [prime_psi_eq_sum_positive, prime_psi_eq_sum_positive,
    Nat.floor_natCast, Nat.floor_div_natCast, Nat.floor_natCast]

lemma prime_convolution_sqrt_hyperbola (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (vonMangoldt * vonMangoldt) n) =
      2 * (∑ d ∈ Icc 1 (Nat.sqrt N),
        vonMangoldt d * Chebyshev.psi ((N : ℝ) / (d : ℝ))) -
          Chebyshev.psi (Real.sqrt (N : ℝ)) ^ 2 := by
  have hpoint (n : ℕ) : (vonMangoldt * vonMangoldt) n =
      ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d) := by
    rw [ArithmeticFunction.mul_apply]
    exact Nat.sum_divisorsAntidiagonal (fun d k : ℕ => vonMangoldt d * vonMangoldt k)
  simp_rw [hpoint]
  rw [finite_positive_divisor_reindex N (fun d k => vonMangoldt d * vonMangoldt k)]
  simp_rw [← Finset.mul_sum]
  rw [finite_symmetric_dirichlet_hyperbola N (Nat.sqrt N)
    (Nat.sqrt_pos.mpr (by omega)) (Nat.sqrt_le N) (Nat.lt_succ_sqrt N)]
  simp_rw [prime_psi_nat, prime_psi_ratio]
  have hs : Chebyshev.psi ((Nat.sqrt N : ℕ) : ℝ) =
      Chebyshev.psi (Real.sqrt (N : ℝ)) := by
    rw [prime_psi_eq_sum_positive, prime_psi_eq_sum_positive,
      Nat.floor_natCast, Real.nat_floor_real_sqrt_eq_nat_sqrt]
  rw [hs]

lemma prime_log_weight_abel_identity (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, vonMangoldt n * Real.log (n : ℝ)) =
      Chebyshev.psi (N : ℝ) * Real.log (N : ℝ) -
        ∫ t in (1 : ℝ)..(N : ℝ), Chebyshev.psi t / t := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ Real.log t := by
    intro t ht
    exact (Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 (N : ℝ)) :=
    continuousOn_id.inv₀ (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hi : IntegrableOn (deriv Real.log) (Set.Icc (1 : ℝ) N) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht =>
      (Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)).deriv.symm)
        measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul (fun n => (vonMangoldt n : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1) hNr hd hi
  simp only [Nat.floor_one, Nat.floor_natCast] at ha
  have hleft : (∑ n ∈ Ioc 1 N, Real.log (n : ℝ) * vonMangoldt n) =
      ∑ n ∈ Icc 1 N, vonMangoldt n * Real.log (n : ℝ) := by
    have he : (∑ n ∈ Ioc 1 N, Real.log (n : ℝ) * vonMangoldt n) =
        ∑ n ∈ Icc 1 N, Real.log (n : ℝ) * vonMangoldt n := by
      apply Finset.sum_subset
      · intro n hn
        simp only [mem_Ioc, mem_Icc] at hn ⊢
        omega
      · intro n hn hnnot
        have hn1 : n = 1 := by
          simp only [mem_Icc, mem_Ioc] at hn hnnot
          omega
        subst n
        simp
    simpa only [mul_comm] using he
  have hint : (∫ t in Set.Ioc (1 : ℝ) N, deriv Real.log t *
      ∑ n ∈ Icc 0 ⌊t⌋₊, vonMangoldt n) =
        ∫ t in (1 : ℝ)..(N : ℝ), Chebyshev.psi t / t := by
    rw [← intervalIntegral.integral_of_le hNr]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNr] at ht
    dsimp only
    rw [(Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)).deriv,
      ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hleft, hint] at ha
  have hpsi : (∑ n ∈ Icc 0 N, vonMangoldt n) = Chebyshev.psi (N : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rw [hpsi] at ha
  simpa only [Real.log_one, zero_mul, sub_zero, mul_comm] using ha

lemma prime_psi_div_intervalIntegrable (N : ℕ) (hN : 1 ≤ N) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.psi t / t) volume 1 N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNr]
  have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 (N : ℝ)) :=
    continuousOn_id.inv₀ (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hb := integrableOn_mul_sum_Icc (fun n => (vonMangoldt n : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1) hc.integrableOn_Icc (m := 0)
  simpa only [Chebyshev.psi_eq_sum_Icc, div_eq_mul_inv, mul_comm] using hb

lemma prime_remainder_div_intervalIntegrable (N : ℕ) (hN : 1 ≤ N) :
    IntervalIntegrable (fun t : ℝ => (Chebyshev.psi t - t) / t) volume 1 N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ((prime_psi_div_intervalIntegrable N hN).sub
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 1 N)).congr ?_
  intro t ht
  rw [Set.uIoc_of_le hNr] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1.le]
  dsimp only
  field_simp

lemma prime_psi_integral_remainder_identity (N : ℕ) (hN : 1 ≤ N) :
    (∫ t in (1 : ℝ)..(N : ℝ), Chebyshev.psi t / t) =
      (N : ℝ) - 1 + ∫ t in (1 : ℝ)..(N : ℝ), (Chebyshev.psi t - t) / t := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi : (∫ t in (1 : ℝ)..(N : ℝ), Chebyshev.psi t / t) =
      ∫ t in (1 : ℝ)..(N : ℝ), (1 + (Chebyshev.psi t - t) / t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNr] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    dsimp only
    field_simp
    ring
  rw [hi, intervalIntegral.integral_add intervalIntegrable_const
    (prime_remainder_div_intervalIntegrable N hN)]
  simp

theorem centered_prime_convolution_sqrt_identity (N : ℕ) (C : ℝ) (hN : 1 ≤ N) :
    let y : ℝ := Real.sqrt (N : ℝ)
    let R : ℝ → ℝ := fun t => Chebyshev.psi t - t
    let r : ℝ := (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d / (d : ℝ)) - Real.log y + C / 2
    (∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)) =
      -1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * R ((N : ℝ) / (d : ℝ))) +
      2 * (N : ℝ) * r - 2 * y * R y - (R y) ^ 2 -
      R (N : ℝ) * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), R t / t := by
  dsimp only
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    prime_convolution_sqrt_hyperbola N hN, prime_log_weight_abel_identity N hN,
    prime_psi_integral_remainder_identity N hN]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel_right,
    nsmul_eq_mul, Real.nat_floor_real_sqrt_eq_nat_sqrt]
  have hs : (∑ d ∈ Icc 1 (Nat.sqrt N),
      vonMangoldt d * Chebyshev.psi ((N : ℝ) / (d : ℝ))) =
      (N : ℝ) * (∑ d ∈ Icc 1 (Nat.sqrt N), vonMangoldt d / (d : ℝ)) +
        (∑ d ∈ Icc 1 (Nat.sqrt N), vonMangoldt d *
          (Chebyshev.psi ((N : ℝ) / (d : ℝ)) - (N : ℝ) / (d : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hs]
  have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hl : 2 * Real.log (Real.sqrt (N : ℝ)) = Real.log (N : ℝ) := by
    rw [Real.log_sqrt (Nat.cast_nonneg N)]
    ring
  nlinarith [hsq, hl]

theorem centered_prime_convolution_sqrt_error_bound (N : ℕ) (C : ℝ) (hN : 1 ≤ N) :
    let y : ℝ := Real.sqrt (N : ℝ)
    let R : ℝ → ℝ := fun t => Chebyshev.psi t - t
    let r : ℝ := (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d / (d : ℝ)) - Real.log y + C / 2
    |∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)| ≤
      1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * |R ((N : ℝ) / (d : ℝ))|) +
      |2 * (N : ℝ) * r - 2 * y * R y| + (R y) ^ 2 +
      |R (N : ℝ)| * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), |R t| / t := by
  let y : ℝ := Real.sqrt (N : ℝ)
  let R : ℝ → ℝ := fun t => Chebyshev.psi t - t
  let r : ℝ := (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d / (d : ℝ)) - Real.log y + C / 2
  let T : ℝ := ∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * R ((N : ℝ) / (d : ℝ))
  let U : ℝ := 2 * (N : ℝ) * r - 2 * y * R y
  let E : ℝ := R (N : ℝ) * Real.log (N : ℝ)
  let I : ℝ := ∫ t in (1 : ℝ)..(N : ℝ), R t / t
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT : |T| ≤ ∑ d ∈ Icc 1 ⌊y⌋₊,
      vonMangoldt d * |R ((N : ℝ) / (d : ℝ))| := by
    dsimp only [T]
    calc
      _ ≤ ∑ d ∈ Icc 1 ⌊y⌋₊, |vonMangoldt d * R ((N : ℝ) / (d : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
  have hE : |E| = |R (N : ℝ)| * Real.log (N : ℝ) := by
    dsimp only [E]
    rw [abs_mul, abs_of_nonneg (Real.log_nonneg hNr)]
  have hI : |I| ≤ ∫ t in (1 : ℝ)..(N : ℝ), |R t| / t := by
    dsimp only [I]
    calc
      _ ≤ ∫ t in (1 : ℝ)..(N : ℝ), |R t / t| :=
        intervalIntegral.abs_integral_le_integral_abs hNr
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hNr] at ht
        dsimp only
        rw [abs_div, abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t)]
  have htriangle : |-1 + 2 * T + U - (R y) ^ 2 - E + I| ≤
      1 + 2 * |T| + |U| + (R y) ^ 2 + |E| + |I| := by
    apply abs_le.mpr
    constructor <;> nlinarith [le_abs_self T, neg_le_abs T,
      le_abs_self U, neg_le_abs U, le_abs_self E, neg_le_abs E,
      le_abs_self I, neg_le_abs I, sq_nonneg (R y)]
  have hid := centered_prime_convolution_sqrt_identity N C hN
  have hid' : (∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)) =
      -1 + 2 * T + U - (R y) ^ 2 - E + I := by
    convert hid using 1 <;> (dsimp only [T, U, E, I, y, R, r]; ring)
  change |∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)| ≤ _
  rw [hid']
  dsimp only at ⊢
  rw [hE] at htriangle
  change |-1 + 2 * T + U - (R y) ^ 2 - E + I| ≤
    1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * |R ((N : ℝ) / (d : ℝ))|) +
      |U| + (R y) ^ 2 + |R (N : ℝ)| * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), |R t| / t
  linarith

theorem centered_prime_convolution_sqrt_certificate (N : ℕ) (C : ℝ) (hN : 1 ≤ N) :
    let y : ℝ := Real.sqrt (N : ℝ)
    let R : ℝ → ℝ := fun t => Chebyshev.psi t - t
    let r : ℝ := (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d / (d : ℝ)) - Real.log y + C / 2
    ((∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)) =
      -1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * R ((N : ℝ) / (d : ℝ))) +
      2 * (N : ℝ) * r - 2 * y * R y - (R y) ^ 2 -
      R (N : ℝ) * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), R t / t) ∧
    (|∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)| ≤
      1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * |R ((N : ℝ) / (d : ℝ))|) +
      |2 * (N : ℝ) * r - 2 * y * R y| + (R y) ^ 2 +
      |R (N : ℝ)| * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), |R t| / t) := by
  exact ⟨centered_prime_convolution_sqrt_identity N C hN,
    centered_prime_convolution_sqrt_error_bound N C hN⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma log_weight_sum_zero_remove (c : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 0 N, c d * Real.log (d : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 N, c d * Real.log (d : ℝ) ^ 2 := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le N)]
  rw [Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, Real.log_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add]
  rfl

lemma log_weight_sum_Ioc_difference (c : ℕ → ℝ) (A N : ℕ) (hAN : A ≤ N) :
    (∑ d ∈ Finset.Ioc A N, c d) =
      (∑ d ∈ Finset.Icc 1 N, c d) - ∑ d ∈ Finset.Icc 1 A, c d := by
  have h := Finset.sum_Ioc_consecutive c (Nat.zero_le A) hAN
  simp only [← Finset.Icc_succ_left_eq_Ioc, Order.succ_eq_add_one, zero_add] at h
  simp only [← Finset.Icc_succ_left_eq_Ioc, Order.succ_eq_add_one] at ⊢
  linarith

lemma hasDerivAt_log_inv_sq (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => (Real.log t ^ 2)⁻¹)
      (-(2 / (t * Real.log t ^ 3))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd := ((Real.hasDerivAt_log ht0).pow 2).inv (pow_ne_zero 2 hl0)
  convert hd using 1
  all_goals first | rfl | (simp only [Pi.pow_apply]; field_simp [hl0, ht0]; ring)

lemma log_weight_deriv_continuous (a x : ℝ) (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => -(2 / (t * Real.log t ^ 3))) (Set.Icc a x) := by
  have ht0 : ∀ t ∈ Set.Icc a x, t ≠ 0 := by
    intro t ht; linarith [ht.1]
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => ht0 t ht)
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht; exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  exact (continuousOn_const.div (continuousOn_id.mul (hl.pow 3))
    (fun t ht => mul_ne_zero (ht0 t ht) (pow_ne_zero 3 (hl0 t ht)))).neg

lemma log_weight_kernel_intervalIntegrable (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x := by
  have hf : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 3)⁻¹) (Set.Icc a x) := by
    have ht0 : ∀ t ∈ Set.Icc a x, t ≠ 0 := by intro t ht; linarith [ht.1]
    have hl : ContinuousOn Real.log (Set.Icc a x) :=
      Real.continuousOn_log.mono (fun t ht => ht0 t ht)
    exact (continuousOn_id.mul (hl.pow 3)).inv₀ (fun t ht =>
      mul_ne_zero (ht0 t ht) (pow_ne_zero 3 (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
  have h := integrableOn_mul_sum_Icc (fun d => c d * Real.log (d : ℝ) ^ 2)
    (by linarith : 0 ≤ a) hf.integrableOn_Icc (m := 1)
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem log_squared_weight_removal_identity (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) := by
  have hd : ∀ t ∈ Set.Icc a x,
      DifferentiableAt ℝ (fun t : ℝ => (Real.log t ^ 2)⁻¹) t := by
    intro t ht; exact (hasDerivAt_log_inv_sq t (lt_of_lt_of_le ha ht.1)).differentiableAt
  have hdv : ∀ t ∈ Set.Icc a x,
      deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹) t = -(2 / (t * Real.log t ^ 3)) := by
    intro t ht; exact (hasDerivAt_log_inv_sq t (lt_of_lt_of_le ha ht.1)).deriv
  have hi : IntegrableOn (deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹)) (Set.Icc a x) :=
    ((log_weight_deriv_continuous a x ha).integrableOn_Icc).congr_fun
      (fun t ht => (hdv t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun d => c d * Real.log (d : ℝ) ^ 2) (by linarith : 0 ≤ a) hax hd hi
  simp_rw [log_weight_sum_zero_remove c] at h
  have hleft :
      (∑ d ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊,
        (Real.log (d : ℝ) ^ 2)⁻¹ * (c d * Real.log (d : ℝ) ^ 2)) =
      (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) - ∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d := by
    rw [← log_weight_sum_Ioc_difference c _ _ (Nat.floor_le_floor hax)]
    apply Finset.sum_congr rfl
    intro d hd
    have hda : a < (d : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ a)).mp (Finset.mem_Ioc.mp hd).1
    have hl : Real.log (d : ℝ) ≠ 0 := (Real.log_pos (lt_trans ha hda)).ne'
    field_simp
  rw [hleft] at h
  have hint :
      (∫ t in Set.Ioc a x, deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹) t *
        ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) =
      -(2 * ∫ t in a..x,
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
          (t * Real.log t ^ 3)) := by
    rw [← intervalIntegral.integral_of_le hax]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    dsimp only
    rw [hdv t ht]
    ring
  rw [hint] at h
  simp only [div_eq_mul_inv, mul_comm ((Real.log _) ^ 2)⁻¹] at h ⊢
  linarith

lemma log_squared_weight_removal_bound (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := by
  let M : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d
  let W : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2
  have hden : ∀ t ∈ Set.Icc a x, 0 < t * Real.log t ^ 3 := by
    intro t ht
    exact mul_pos (by linarith [ht.1]) (pow_pos (Real.log_pos (lt_of_lt_of_le ha ht.1)) 3)
  have hrem : |∫ t in a..x, W t / (t * Real.log t ^ 3)| ≤
      ∫ t in a..x, |W t| / (t * Real.log t ^ 3) := by
    calc
      _ ≤ ∫ t in a..x, |W t / (t * Real.log t ^ 3)| :=
        intervalIntegral.abs_integral_le_integral_abs hax
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hax] at ht
        dsimp only
        rw [abs_div, abs_of_pos (hden t ht)]
  have hid := log_squared_weight_removal_identity c a x ha hax
  change M x = (M a - W a / Real.log a ^ 2) + W x / Real.log x ^ 2 +
    2 * ∫ t in a..x, W t / (t * Real.log t ^ 3) at hid
  change |M x| ≤ |M a - W a / Real.log a ^ 2| + |W x| / Real.log x ^ 2 +
    2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3)
  rw [hid]
  have h1 := abs_add_le (M a - W a / Real.log a ^ 2) (W x / Real.log x ^ 2)
  have h2 := abs_add_le ((M a - W a / Real.log a ^ 2) + W x / Real.log x ^ 2)
    (2 * ∫ t in a..x, W t / (t * Real.log t ^ 3))
  have hW : |W x / Real.log x ^ 2| = |W x| / Real.log x ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos (Real.log_pos (lt_of_lt_of_le ha hax)) 2)]
  have h3 : |2 * ∫ t in a..x, W t / (t * Real.log t ^ 3)| ≤
      2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hrem (by norm_num)
  rw [hW] at h1
  linarith

theorem log_squared_weight_removal_certificate (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x ∧
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) ∧
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := by
  exact ⟨log_weight_kernel_intervalIntegrable c a x ha hax,
    log_squared_weight_removal_identity c a x ha hax,
    log_squared_weight_removal_bound c a x ha hax⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma prime_harmonic_abel_identity (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      (∑ n ∈ Icc 1 ⌊a⌋₊, vonMangoldt n / (n : ℝ)) +
      Chebyshev.psi x / x - Chebyshev.psi a / a +
      ∫ t in a..x, Chebyshev.psi t / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc a x, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).differentiableAt
  have hcder : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc a x) :=
    ((continuousOn_id.pow 2).inv₀
      (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc a x) := by
    simpa only [deriv_inv'] using hcder.integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (fun n => (vonMangoldt n : ℝ))
    ha.le hax hd hi
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at h
  have hleft : (∑ n ∈ Ioc ⌊a⌋₊ ⌊x⌋₊, (n : ℝ)⁻¹ * vonMangoldt n) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) -
        ∑ n ∈ Icc 1 ⌊a⌋₊, vonMangoldt n / (n : ℝ) := by
    rw [← log_weight_sum_Ioc_difference (fun n => vonMangoldt n / (n : ℝ))
      _ _ (Nat.floor_le_floor hax)]
    apply Finset.sum_congr rfl
    intro n hn
    rw [div_eq_mul_inv, mul_comm]
  rw [hleft] at h
  have hint : (∫ t in Set.Ioc a x, deriv (fun t : ℝ => t⁻¹) t * Chebyshev.psi t) =
      -(∫ t in a..x, Chebyshev.psi t / t ^ 2) := by
    rw [← intervalIntegral.integral_of_le hax]
    simp_rw [deriv_inv, neg_mul, mul_comm ((_)⁻¹), ← div_eq_mul_inv]
    exact intervalIntegral.integral_neg
  rw [hint] at h
  simp only [div_eq_mul_inv, mul_comm] at h ⊢
  linarith

lemma prime_remainder_square_div_intervalIntegrable (a x : ℝ)
    (ha : 0 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) volume a x := by
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a x) :=
    (continuousOn_id.pow 2).inv₀
      (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
  have hb := integrableOn_mul_sum_Icc (fun n => (vonMangoldt n : ℝ))
    ha.le hc.integrableOn_Icc (m := 0)
  have hψ : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t / t ^ 2) volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    simpa only [Chebyshev.psi_eq_sum_Icc, div_eq_mul_inv, mul_comm] using hb
  have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    exact (continuousOn_id.inv₀
      (fun t ht => by change t ≠ 0; linarith [ht.1])).integrableOn_Icc
  refine (hψ.sub hi).congr ?_
  intro t ht
  rw [Set.uIoc_of_le hax] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1.le]
  dsimp only
  field_simp

theorem centered_first_mertens_increment (a x C : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    ((∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) - Real.log x + C / 2 -
      (Chebyshev.psi x - x) / x) =
      ((∑ n ∈ Icc 1 ⌊a⌋₊, vonMangoldt n / (n : ℝ)) - Real.log a + C / 2 -
        (Chebyshev.psi a - a) / a) +
      ∫ t in a..x, (Chebyshev.psi t - t) / t ^ 2 := by
  have hx : 0 < x := ha.trans_le hax
  have hiR := prime_remainder_square_div_intervalIntegrable a x ha hax
  have hiinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    exact (continuousOn_id.inv₀
      (fun t ht => by change t ≠ 0; linarith [ht.1])).integrableOn_Icc
  have hint : (∫ t in a..x, Chebyshev.psi t / t ^ 2) =
      (∫ t in a..x, (Chebyshev.psi t - t) / t ^ 2) + Real.log x - Real.log a := by
    have he : (∫ t in a..x, Chebyshev.psi t / t ^ 2) =
        ∫ t in a..x, ((Chebyshev.psi t - t) / t ^ 2 + t⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hax] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      dsimp only
      field_simp
      ring
    rw [he, intervalIntegral.integral_add hiR hiinv,
      integral_inv_of_pos ha hx, Real.log_div hx.ne' ha.ne']
    ring
  rw [prime_harmonic_abel_identity a x ha hax, hint]
  field_simp [ha.ne', hx.ne']
  ring

theorem centered_first_mertens_tail_certificate (x : ℝ) (hx : 1 ≤ x)
    (hR : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2)
      (Set.Ioi 1)) :
    let C : ℝ := -2 * (1 + ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2)
    let E : ℝ := (∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) - Real.log x + C / 2 -
      (Chebyshev.psi x - x) / x
    E = -(∫ t in Set.Ioi x, (Chebyshev.psi t - t) / t ^ 2) ∧
      |E| ≤ ∫ t in Set.Ioi x, |Chebyshev.psi t - t| / t ^ 2 := by
  let C : ℝ := -2 * (1 + ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2)
  have hinc := centered_first_mertens_increment 1 x C (by norm_num) hx
  have hψone : Chebyshev.psi (1 : ℝ) = 0 := by
    rw [prime_psi_eq_sum_positive]
    norm_num
  simp only [Nat.floor_one, Finset.Icc_self, Finset.sum_singleton,
    vonMangoldt_apply_one, zero_div, Real.log_one, hψone] at hinc
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hR hx
  have he : ((∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) - Real.log x + C / 2 -
      (Chebyshev.psi x - x) / x) =
      -(∫ t in Set.Ioi x, (Chebyshev.psi t - t) / t ^ 2) := by
    dsimp only [C] at hinc
    linarith
  change _ = _ ∧ _ ≤ _
  constructor
  · exact he
  · rw [he, abs_neg]
    have hnorm := norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioi x)) (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2)
    simpa only [Real.norm_eq_abs, abs_div, abs_sq] using hnorm

theorem centered_prime_convolution_tail_certificate_complete (N : ℕ) (hN : 1 ≤ N)
    (hR : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2)
      (Set.Ioi 1)) :
    let C : ℝ := -2 * (1 + ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2)
    let y : ℝ := Real.sqrt (N : ℝ)
    let R : ℝ → ℝ := fun t => Chebyshev.psi t - t
    let r : ℝ := (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d / (d : ℝ)) - Real.log y + C / 2
    (2 * (N : ℝ) * r - 2 * y * R y =
      -2 * (N : ℝ) * ∫ t in Set.Ioi y, R t / t ^ 2) ∧
    (|∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)| ≤
      1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * |R ((N : ℝ) / (d : ℝ))|) +
      2 * (N : ℝ) * (∫ t in Set.Ioi y, |R t| / t ^ 2) + (R y) ^ 2 +
      |R (N : ℝ)| * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), |R t| / t) := by
  let C : ℝ := -2 * (1 + ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2)
  let y : ℝ := Real.sqrt (N : ℝ)
  let R : ℝ → ℝ := fun t => Chebyshev.psi t - t
  let r : ℝ := (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d / (d : ℝ)) - Real.log y + C / 2
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hy : 1 ≤ y := by
    dsimp only [y]
    exact (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr (by nlinarith)
  have hyp : 0 < y := by linarith
  have hsq : y ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have htail := centered_first_mertens_tail_certificate y hy hR
  change (r - R y / y) = -(∫ t in Set.Ioi y, R t / t ^ 2) ∧
    |r - R y / y| ≤ (∫ t in Set.Ioi y, |R t| / t ^ 2) at htail
  have hU : 2 * (N : ℝ) * r - 2 * y * R y = 2 * (N : ℝ) * (r - R y / y) := by
    rw [← hsq]
    field_simp [hyp.ne']
  have hUeq : 2 * (N : ℝ) * r - 2 * y * R y =
      -2 * (N : ℝ) * ∫ t in Set.Ioi y, R t / t ^ 2 := by
    rw [hU, htail.1]
    ring
  have hUbound : |2 * (N : ℝ) * r - 2 * y * R y| ≤
      2 * (N : ℝ) * (∫ t in Set.Ioi y, |R t| / t ^ 2) := by
    rw [hU, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * N)]
    exact mul_le_mul_of_nonneg_left htail.2 (by positivity)
  have hb := centered_prime_convolution_sqrt_error_bound N C hN
  change |∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)| ≤
    1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * |R ((N : ℝ) / (d : ℝ))|) +
    |2 * (N : ℝ) * r - 2 * y * R y| + (R y) ^ 2 +
    |R (N : ℝ)| * Real.log (N : ℝ) +
    ∫ t in (1 : ℝ)..(N : ℝ), |R t| / t at hb
  change _ = _ ∧ _ ≤ _
  exact ⟨hUeq, by linarith⟩

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

theorem solution  (N : ℕ) (hN : 1 ≤ N)
    (hR : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2)
      (Set.Ioi 1)) :
    let C : ℝ := -2 * (1 + ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2)
    let y : ℝ := Real.sqrt (N : ℝ)
    let R : ℝ → ℝ := fun t => Chebyshev.psi t - t
    let r : ℝ := (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d / (d : ℝ)) - Real.log y + C / 2
    (2 * (N : ℝ) * r - 2 * y * R y =
      -2 * (N : ℝ) * ∫ t in Set.Ioi y, R t / t ^ 2) ∧
    (|∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)| ≤
      1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * |R ((N : ℝ) / (d : ℝ))|) +
      2 * (N : ℝ) * (∫ t in Set.Ioi y, |R t| / t ^ 2) + (R y) ^ 2 +
      |R (N : ℝ)| * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), |R t| / t) := Helfgott.centered_prime_convolution_tail_certificate_complete N hN hR
#print axioms solution
