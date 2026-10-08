-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_partial_sum_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T16:05:35.430291+00:00
-- url     : https://prove2.me/submissions/5d6781e9-019c-47fd-9805-fe1b07c0958e

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.SuccPred

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

lemma moebius_finite_floor_sum (N : ℕ) (hN : 1≤N) :
    (∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)*(N/d : ℕ))=1 := by
  have hdiv : (∑ n∈Finset.Icc 1 N,∑ d∈n.divisors,((moebius d : ℤ) : ℝ))=1 := by
    have he (n : ℕ) (hn : n∈Finset.Icc 1 N) :
        (∑ d∈n.divisors,((moebius d : ℤ) : ℝ))=if n=1 then (1:ℝ) else 0 := by
      exact_mod_cast moebius_divisor_sum n (by have h:1≤n:=(Finset.mem_Icc.mp hn).1;omega)
    rw [Finset.sum_congr rfl he]
    simp [Finset.mem_Icc,hN]
  have hr := finite_positive_divisor_reindex N (fun d _ => ((moebius d : ℤ) : ℝ))
  simp only [Finset.sum_const,Nat.card_Icc,smul_eq_mul] at hr
  norm_num only [Nat.add_sub_cancel] at hr
  rw [hr] at hdiv
  simpa only [nsmul_eq_mul,mul_comm] using hdiv

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma natural_division_fraction_bounds (N d : ℕ) (hd : 1≤d) :
    0≤(N : ℝ)/(d : ℝ)-(N/d : ℕ) ∧ (N : ℝ)/(d : ℝ)-(N/d : ℕ)≤1 := by
  have hdR : (0:ℝ)<(d : ℝ) := by exact_mod_cast hd
  have hlow : ((N/d : ℕ) : ℝ)≤(N : ℝ)/(d : ℝ) := Nat.cast_div_le
  have hupN : N<((N/d)+1)*d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (N/d))
  have hup : (N : ℝ)<(((N/d : ℕ) : ℝ)+1)*(d : ℝ) := by exact_mod_cast hupN
  have hf : (N : ℝ)/(d : ℝ)<((N/d : ℕ) : ℝ)+1 := (div_lt_iff₀ hdR).mpr hup
  constructor <;> linarith

theorem moebius_reciprocal_partial_sum_abs_le_one_complete (N : ℕ) :
    |∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)/(d : ℝ)|≤1 := by
  by_cases hN : N=0
  · subst N
    simp
  have hNp : 1≤N := Nat.pos_of_ne_zero hN
  let delta : ℕ→ℝ := fun d => (N : ℝ)/(d : ℝ)-(N/d : ℕ)
  have hmain : (N : ℝ)*(∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)/(d : ℝ))=
      1+(∑ d∈Finset.Icc 2 N,((moebius d : ℤ) : ℝ)*delta d) := by
    have hexact : (N : ℝ)*(∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)/(d : ℝ))=
        (∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)*(N/d : ℕ))+
        (∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)*delta d) := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [delta]
      ring
    rw [moebius_finite_floor_sum N hNp] at hexact
    have hsplit : (∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)*delta d)=
        ∑ d∈Finset.Icc 2 N,((moebius d : ℤ) : ℝ)*delta d := by
      rw [←Finset.insert_Icc_succ_left_eq_Icc hNp]
      rw [Finset.sum_insert (by simp)]
      simp [delta]
    rw [hsplit] at hexact
    exact hexact
  have herr : |∑ d∈Finset.Icc 2 N,((moebius d : ℤ) : ℝ)*delta d|≤(N : ℝ)-1 := by
    apply (abs_sum_le_sum_abs _ _).trans
    have hterm : (∑ d∈Finset.Icc 2 N,|((moebius d : ℤ) : ℝ)*delta d|)≤
        ∑ d∈Finset.Icc 2 N,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 1≤d := by have h:2≤d:=(Finset.mem_Icc.mp hd).1;omega
      have hf := natural_division_fraction_bounds N d hdpos
      have hmu : |((moebius d : ℤ) : ℝ)|≤1 := by exact_mod_cast (abs_moebius_le_one (n:=d))
      dsimp [delta]
      rw [abs_mul,abs_of_nonneg hf.1]
      nlinarith [abs_nonneg ((moebius d : ℤ) : ℝ)]
    have hcard : (Finset.Icc 2 N).card=N-1 := by rw [Nat.card_Icc];omega
    simpa only [Finset.sum_const,nsmul_eq_mul,hcard,mul_one,Nat.cast_sub hNp,Nat.cast_one] using hterm
  have hbound : |(N : ℝ)*(∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)/(d : ℝ))|≤(N : ℝ) := by
    rw [hmain]
    have h := (abs_add_le (1:ℝ) (∑ d∈Finset.Icc 2 N,((moebius d : ℤ) : ℝ)*delta d)).trans
      (add_le_add_right herr |(1:ℝ)|)
    norm_num only [abs_one] at h
    linarith
  rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤N)] at hbound
  have hNpR : (0:ℝ)<(N : ℝ) := by exact_mod_cast hNp
  nlinarith

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (N : ℕ) :
    |∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)/(d : ℝ)|≤1 := Helfgott.moebius_reciprocal_partial_sum_abs_le_one_complete N

#print axioms solution
