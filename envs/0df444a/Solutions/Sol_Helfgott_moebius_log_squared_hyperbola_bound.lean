-- Prove2me | solution 1 for Helfgott.moebius_log_squared_hyperbola_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:49:00.329546+00:00
-- url     : https://prove2.me/submissions/9c1b3ea0-4581-49f1-9426-e141fac4ffd0

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield

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
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def logWeightAF (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * Real.log (n : ℝ), by simp⟩

@[simp] lemma logWeightAF_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    logWeightAF f n = f n * Real.log (n : ℝ) := rfl

lemma logWeightAF_neg (f : ArithmeticFunction ℝ) :
    logWeightAF (-f) = -logWeightAF f := by
  ext n
  simp only [logWeightAF_apply, ArithmeticFunction.neg_apply, neg_mul]

lemma logWeightAF_mul (f g : ArithmeticFunction ℝ) :
    logWeightAF (f * g) = logWeightAF f * g + f * logWeightAF g := by
  ext n
  simp only [logWeightAF_apply, ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
  have he : (p.1 : ℝ) * (p.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← he, Real.log_mul (Nat.cast_ne_zero.mpr hp0.1) (Nat.cast_ne_zero.mpr hp0.2)]
  ring

lemma logWeightAF_moebius :
    logWeightAF (moebius : ArithmeticFunction ℝ) =
      -((moebius : ArithmeticFunction ℝ) * vonMangoldt) := by
  have hz : logWeightAF (moebius : ArithmeticFunction ℝ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = -vonMangoldt := by
    ext n
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    simp only [logWeightAF_apply, ArithmeticFunction.intCoe_apply, ArithmeticFunction.neg_apply]
    exact ArithmeticFunction.sum_moebius_mul_log_eq
  have h := congrArg (fun f : ArithmeticFunction ℝ => f * (moebius : ArithmeticFunction ℝ)) hz
  rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one] at h
  calc
    _ = -vonMangoldt * (moebius : ArithmeticFunction ℝ) := h
    _ = -((moebius : ArithmeticFunction ℝ) * vonMangoldt) := by ring

lemma logWeightAF_moebius_squared :
    logWeightAF (logWeightAF (moebius : ArithmeticFunction ℝ)) =
      (moebius : ArithmeticFunction ℝ) *
        (vonMangoldt * vonMangoldt - logWeightAF vonMangoldt) := by
  rw [logWeightAF_moebius, logWeightAF_neg, logWeightAF_mul, logWeightAF_moebius]
  ring

theorem moebius_log_squared_pointwise_convolution (n : ℕ) :
    ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2 =
      ∑ p ∈ n.divisorsAntidiagonal, ((moebius p.1 : ℤ) : ℝ) *
        ((vonMangoldt * vonMangoldt) p.2 - vonMangoldt p.2 * Real.log (p.2 : ℝ)) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) logWeightAF_moebius_squared
  rw [logWeightAF_apply, logWeightAF_apply, ArithmeticFunction.mul_apply] at h
  simp only [ArithmeticFunction.intCoe_apply, sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply, logWeightAF_apply] at h
  simp only [← sub_eq_add_neg] at h
  calc
    _ = ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
    _ = _ := h

theorem moebius_log_squared_summatory_convolution (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) *
        ∑ k ∈ Finset.Icc 1 ⌊x / (d : ℝ)⌋₊,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ)) := by
  have hpoint (n : ℕ) :
      ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2 =
        ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) *
          ((vonMangoldt * vonMangoldt) (n / d) -
            vonMangoldt (n / d) * Real.log (n / d : ℕ)) := by
    rw [moebius_log_squared_pointwise_convolution]
    exact Nat.sum_divisorsAntidiagonal (fun d k : ℕ => ((moebius d : ℤ) : ℝ) *
      ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ)))
  simp_rw [hpoint]
  rw [finite_positive_divisor_reindex ⌊x⌋₊ (fun d k : ℕ => ((moebius d : ℤ) : ℝ) *
    ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ)))]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.floor_div_natCast, Finset.mul_sum]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma moebius_real_floor_kernel_one (x : ℝ) (hx : 1 ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
      ((moebius d : ℤ) : ℝ) * (⌊x / (d : ℝ)⌋₊ : ℝ)) = 1 := by
  let N := ⌊x⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hx : ((1 : ℕ) : ℝ) ≤ x)
  have hdiv (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ)) = if n = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
      (coe_moebius_mul_coe_zeta (R := ℝ))
    rw [ArithmeticFunction.coe_mul_zeta_apply] at h
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    simpa only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply,
      hn0, if_false] using h
  have hleft : (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
      ((moebius d : ℤ) : ℝ)) = 1 := by
    rw [Finset.sum_congr rfl hdiv]
    simp [Finset.mem_Icc, hN]
  have hreindex := finite_positive_divisor_reindex N
    (fun d _ => ((moebius d : ℤ) : ℝ))
  rw [hleft] at hreindex
  rw [hreindex]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.floor_div_natCast]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel_right,
    nsmul_eq_mul, N]
  ring

theorem moebius_log_squared_centered_convolution (x C : ℝ) (hx : 1 ≤ x) :
    C + (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2) =
    ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) *
      ((∑ k ∈ Finset.Icc 1 ⌊x / (d : ℝ)⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ))) +
        C * (⌊x / (d : ℝ)⌋₊ : ℝ)) := by
  rw [moebius_log_squared_summatory_convolution]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hconstant :
      (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) *
        (C * (⌊x / (d : ℝ)⌋₊ : ℝ))) = C := by
    calc
      _ = C * (∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
          ((moebius d : ℤ) : ℝ) * (⌊x / (d : ℝ)⌋₊ : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = C := by rw [moebius_real_floor_kernel_one x hx, mul_one]
  rw [hconstant, add_comm]

lemma abs_moebius_real_eq_square (n : ℕ) :
    |((moebius n : ℤ) : ℝ)| = ((moebius n : ℤ) : ℝ) ^ 2 := by
  rcases moebius_eq_or n with h | h | h <;> simp [h]

theorem moebius_log_squared_bound_of_centered_prime_error
    (x C : ℝ) (E : ℝ → ℝ) (hx : 1 ≤ x)
    (hE : ∀ d ∈ Finset.Icc 1 ⌊x⌋₊,
      |(∑ k ∈ Finset.Icc 1 ⌊x / (d : ℝ)⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ))) +
        C * (⌊x / (d : ℝ)⌋₊ : ℝ)| ≤ E (x / (d : ℝ))) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      |C| + ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        ((moebius d : ℤ) : ℝ) ^ 2 * E (x / (d : ℝ)) := by
  let W : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2
  have hcenter : |C + W| ≤ ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
      ((moebius d : ℤ) : ℝ) ^ 2 * E (x / (d : ℝ)) := by
    dsimp only [W]
    rw [moebius_log_squared_centered_convolution x C hx]
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
          |((moebius d : ℤ) : ℝ) *
            ((∑ k ∈ Finset.Icc 1 ⌊x / (d : ℝ)⌋₊,
              ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ))) +
              C * (⌊x / (d : ℝ)⌋₊ : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro d hd
        rw [abs_mul, abs_moebius_real_eq_square]
        exact mul_le_mul_of_nonneg_left (hE d hd) (sq_nonneg _)
  change |W| ≤ _
  have htriangle : |W| ≤ |C + W| + |C| := by
    have h := abs_sub (C + W) C
    simpa only [add_sub_cancel_left] using h
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem moebius_log_squared_hyperbola_identity (N K : ℕ) (C : ℝ)
    (hN : 1 ≤ N) (hK : 0 < K) :
    C + (∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2) =
      (∑ d ∈ Icc 1 (N / K), ((moebius d : ℤ) : ℝ) *
        ∑ k ∈ Icc 1 (N / d),
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)) +
      (∑ k ∈ Icc 1 K,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C) *
          ∑ d ∈ Icc 1 (N / k), ((moebius d : ℤ) : ℝ)) -
      (∑ d ∈ Icc 1 (N / K), ((moebius d : ℤ) : ℝ)) *
        (∑ k ∈ Icc 1 K,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)) := by
  have hcenter := moebius_log_squared_centered_convolution (N : ℝ) C
    (by exact_mod_cast hN)
  simp only [Nat.floor_natCast, Nat.floor_div_natCast] at hcenter
  have he (d : ℕ) :
      (∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ))) +
        C * (N / d : ℕ) =
      ∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel_right, nsmul_eq_mul]
    ring
  simp_rw [he] at hcenter
  exact hcenter.trans (finite_dirichlet_hyperbola N K hK
    (fun d => ((moebius d : ℤ) : ℝ))
    (fun k => (vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C))

lemma nat_div_cast_le_real_div (N k : ℕ) (hk : 0 < k) :
    ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / (k : ℝ) := by
  have hp : (0 : ℝ) < k := by exact_mod_cast hk
  apply (le_div_iff₀ hp).mpr
  exact_mod_cast Nat.div_mul_le_self N k

theorem moebius_log_squared_hyperbola_bound_complete (N K : ℕ) (C L : ℝ) (E : ℝ → ℝ)
    (hN : 1 ≤ N) (hK : 0 < K) (hL : 0 < L)
    (hR : ∀ d ∈ Icc 1 (N / K),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          E ((N : ℝ) / (d : ℝ)))
    (hM : ∀ u : ℕ, N / K ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / L) :
    |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      |C| + (∑ d ∈ Icc 1 (N / K),
        ((moebius d : ℤ) : ℝ) ^ 2 * E ((N : ℝ) / (d : ℝ))) +
      ((N : ℝ) / L) *
        ((∑ k ∈ Icc 1 K,
          |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
            (k : ℝ)) +
          |∑ k ∈ Icc 1 K,
            ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
            (K : ℝ)) := by
  let a : ℕ → ℝ := fun k =>
    (vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C
  let M : ℕ → ℝ := fun u => ∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)
  let big : ℝ := ∑ d ∈ Icc 1 (N / K), ((moebius d : ℤ) : ℝ) *
    ∑ k ∈ Icc 1 (N / d), a k
  let small : ℝ := ∑ k ∈ Icc 1 K, a k * M (N / k)
  let boundary : ℝ := M (N / K) * ∑ k ∈ Icc 1 K, a k
  let W : ℝ := ∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2
  have hidentity : C + W = big + small - boundary :=
    moebius_log_squared_hyperbola_identity N K C hN hK
  have hbig : |big| ≤ ∑ d ∈ Icc 1 (N / K),
      ((moebius d : ℤ) : ℝ) ^ 2 * E ((N : ℝ) / (d : ℝ)) := by
    dsimp only [big]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    rw [abs_mul, abs_moebius_real_eq_square]
    exact mul_le_mul_of_nonneg_left (hR d hd) (sq_nonneg _)
  have hsmallM (k : ℕ) (hk : k ∈ Icc 1 K) :
      |M (N / k)| ≤ ((N : ℝ) / L) / (k : ℝ) := by
    have hkpos : 0 < k := (mem_Icc.mp hk).1
    have hm := hM (N / k) (Nat.div_le_div_left (mem_Icc.mp hk).2 hkpos)
    have hd := div_le_div_of_nonneg_right (nat_div_cast_le_real_div N k hkpos) hL.le
    have he : ((N : ℝ) / (k : ℝ)) / L = ((N : ℝ) / L) / (k : ℝ) := by ring
    exact hm.trans (he ▸ hd)
  have hsmall : |small| ≤ ((N : ℝ) / L) *
      ∑ k ∈ Icc 1 K, |a k| / (k : ℝ) := by
    dsimp only [small]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [abs_mul]
    calc
      _ ≤ |a k| * (((N : ℝ) / L) / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (hsmallM k hk) (abs_nonneg _)
      _ = _ := by ring
  have hboundary : |boundary| ≤ ((N : ℝ) / L) *
      |∑ k ∈ Icc 1 K, a k| / (K : ℝ) := by
    have hm := hM (N / K) le_rfl
    have hd := div_le_div_of_nonneg_right (nat_div_cast_le_real_div N K hK) hL.le
    have hc : |M (N / K)| ≤ ((N : ℝ) / L) / (K : ℝ) := by
      have he : ((N : ℝ) / (K : ℝ)) / L = ((N : ℝ) / L) / (K : ℝ) := by ring
      exact hm.trans (he ▸ hd)
    dsimp only [boundary]
    rw [abs_mul]
    calc
      _ ≤ (((N : ℝ) / L) / (K : ℝ)) * |∑ k ∈ Icc 1 K, a k| :=
        mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ = _ := by ring
  have htriangle : |W| ≤ |C| + |big| + |small| + |boundary| := by
    have h1 := abs_sub (C + W) C
    have h2 := abs_sub (big + small) boundary
    have h3 := abs_add_le big small
    rw [hidentity] at h1
    have hw : big + small - boundary - C = W := by linarith
    rw [hw] at h1
    linarith
  change |W| ≤ _
  change |W| ≤ |C| + (∑ d ∈ Icc 1 (N / K),
    ((moebius d : ℤ) : ℝ) ^ 2 * E ((N : ℝ) / (d : ℝ))) +
    ((N : ℝ) / L) * ((∑ k ∈ Icc 1 K, |a k| / (k : ℝ)) +
      |∑ k ∈ Icc 1 K, a k| / (K : ℝ))
  have he : ((N : ℝ) / L) *
      ((∑ k ∈ Icc 1 K, |a k| / (k : ℝ)) +
        |∑ k ∈ Icc 1 K, a k| / (K : ℝ)) =
      ((N : ℝ) / L) * (∑ k ∈ Icc 1 K, |a k| / (k : ℝ)) +
        ((N : ℝ) / L) * |∑ k ∈ Icc 1 K, a k| / (K : ℝ) := by ring
  rw [he]
  linarith

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution  (N K : ℕ) (C L : ℝ) (E : ℝ → ℝ)
    (hN : 1 ≤ N) (hK : 0 < K) (hL : 0 < L)
    (hR : ∀ d ∈ Icc 1 (N / K),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          E ((N : ℝ) / (d : ℝ)))
    (hM : ∀ u : ℕ, N / K ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / L) :
    |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      |C| + (∑ d ∈ Icc 1 (N / K),
        ((moebius d : ℤ) : ℝ) ^ 2 * E ((N : ℝ) / (d : ℝ))) +
      ((N : ℝ) / L) *
        ((∑ k ∈ Icc 1 K,
          |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
            (k : ℝ)) +
          |∑ k ∈ Icc 1 K,
            ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
            (K : ℝ)) := Helfgott.moebius_log_squared_hyperbola_bound_complete N K C L E hN hK hL hR hM
#print axioms solution
