-- Prove2me | solution 1 for Helfgott.moebius_finite_logarithmic_kernel_identity
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T16:55:23.005189+00:00
-- url     : https://prove2.me/submissions/ad4ebb2f-69c2-4d91-a978-5e9918294d66

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro hroot
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have h : p ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa [pow_two] using hdvd)
    rw [hroot] at h
    exact hp.ne_one (Nat.dvd_one.mp h)
  · intro hsf
    have h := hsf (Nat.floorRoot 2 n) (by simpa [pow_two] using Nat.floorRoot_pow_dvd (n:=2) (a:=n))
    exact Nat.isUnit_iff.mp h

lemma moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
    (moebius n)^2 = ∑ d ∈ n.divisors,if d^2 ∣ n then moebius d else 0 := by
  have hroot0 : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by norm_num,hn⟩
  have he : n.divisors.filter (fun d => d^2 ∣ n) = (Nat.floorRoot 2 n).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hsq⟩
      exact ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp hsq,hroot0⟩
    · rintro ⟨hd,hr0⟩
      have hsq := Nat.pow_dvd_iff_dvd_floorRoot.mpr hd
      exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn⟩,hsq⟩
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [floorRoot_two_eq_one_iff_squarefree n hn]

lemma coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,if e ∣ n then moebius e else 0) =
      if Nat.Coprime n q then 1 else 0 := by
  have he : q.divisors.filter (fun e => e ∣ n) = (Nat.gcd n q).divisors := by
    ext e
    simp only [Finset.mem_filter,Nat.mem_divisors]
    have hg : Nat.gcd n q ≠ 0 := Nat.gcd_ne_zero_right hq
    constructor
    · rintro ⟨⟨heq,hq0⟩,hen⟩
      exact ⟨Nat.dvd_gcd hen heq,hg⟩
    · rintro ⟨heg,hg0⟩
      exact ⟨⟨dvd_trans heg (Nat.gcd_dvd_right n q),hq⟩,dvd_trans heg (Nat.gcd_dvd_left n q)⟩
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast coprime_moebius_divisor_expansion q n hq
  rw [hcop]
  by_cases h : Nat.Coprime n q
  · simp only [if_pos h,mul_one]
    have he : (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
        ∑ d ∈ n.divisors,if d^2 ∣ n then ((moebius d : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdc : Nat.Coprime d q := h.of_dvd_left (Nat.dvd_of_mem_divisors hd)
      by_cases hs : d^2 ∣ n <;> simp [hs,hdc]
    rw [he]
    exact_mod_cast moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem moebius_finite_logarithmic_kernel_identity_complete (N : ℕ) (hN : 1 ≤ N) :
    (∑ d∈Finset.Icc 1 N,∑ k∈Finset.Icc 1 (N/d),
      ((moebius d : ℤ) : ℝ)*Real.log ((N : ℝ)/((d*k : ℕ) : ℝ))) = Real.log (N : ℝ) := by
  have hr := finite_positive_divisor_reindex N
    (fun d k => ((moebius d : ℤ) : ℝ)*Real.log ((N : ℝ)/((d*k : ℕ) : ℝ)))
  have he (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      (∑ d∈n.divisors,((moebius d : ℤ) : ℝ)*Real.log ((N : ℝ)/((d*(n/d) : ℕ) : ℝ))) =
        (if n=1 then (1:ℝ) else 0)*Real.log ((N : ℝ)/(n : ℝ)) := by
    have hn0 : n≠0 := by have hh := (Finset.mem_Icc.mp hn).1;omega
    have hemul : ∀ d∈n.divisors,d*(n/d)=n := fun d hd => Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    rw [Finset.sum_congr rfl (fun d hd => by rw [hemul d hd]),←Finset.sum_mul]
    have hm : (∑ d∈n.divisors,((moebius d : ℤ) : ℝ))=if n=1 then 1 else 0 := by
      exact_mod_cast moebius_divisor_sum n hn0
    rw [hm]
  rw [←hr,Finset.sum_congr rfl he]
  simp [Finset.mem_Icc,hN]

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (N : ℕ) (hN : 1 ≤ N) :
    (∑ d∈Finset.Icc 1 N,∑ k∈Finset.Icc 1 (N/d),
      ((moebius d : ℤ) : ℝ)*Real.log ((N : ℝ)/((d*k : ℕ) : ℝ))) = Real.log (N : ℝ) := Helfgott.moebius_finite_logarithmic_kernel_identity_complete N hN

#print axioms solution
