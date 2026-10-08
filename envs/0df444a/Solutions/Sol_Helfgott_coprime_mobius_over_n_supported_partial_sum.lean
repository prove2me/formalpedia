-- Prove2me | solution 1 for Helfgott.coprime_mobius_over_n_supported_partial_sum
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T15:53:19.713397+00:00
-- url     : https://prove2.me/submissions/4b19f26e-e6f8-4a14-8cf6-e0ea33b44440

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def coprimeMobiusAF (q : ℕ) : ArithmeticFunction ℝ where
  toFun n := if Nat.Coprime n q then ((moebius n : ℤ) : ℝ) else 0
  map_zero' := by simp

noncomputable def primeSupportedAF (q : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => if p∣q then 1 else 0)

lemma coprimeMobiusAF_multiplicative (q : ℕ) : (coprimeMobiusAF q).IsMultiplicative := by
  refine ⟨by simp [coprimeMobiusAF],?_⟩
  intro m n hmn
  change (if Nat.Coprime (m*n) q then ((moebius (m*n) : ℤ) : ℝ) else 0)=_
  change _=(if Nat.Coprime m q then ((moebius m : ℤ) : ℝ) else 0)*
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ) else 0)
  have hmu : ((moebius (m*n) : ℤ) : ℝ)=((moebius m : ℤ) : ℝ)*((moebius n : ℤ) : ℝ) := by
    exact_mod_cast isMultiplicative_moebius.map_mul_of_coprime hmn
  rw [hmu]
  split_ifs <;> simp_all only [Nat.coprime_mul_iff_left] <;> aesop

lemma coprimeMobiusAF_prime_pow_sum (q p k : ℕ) (hp : Nat.Prime p) :
    (∑ i∈Finset.range (k+1),coprimeMobiusAF q (p^i))=
      if k=0 then 1 else if p∣q then 1 else 0 := by
  cases k with
  | zero => simp [coprimeMobiusAF]
  | succ k =>
    rw [Finset.sum_range_succ']
    have hsum : (∑ i∈Finset.range (k+1),coprimeMobiusAF q (p^(i+1)))=
        if p∣q then 0 else -1 := by
      rw [Finset.sum_eq_single 0]
      · norm_num only [Nat.zero_add,pow_one]
        change (if Nat.Coprime p q then ((moebius p : ℤ) : ℝ) else 0)=_
        rw [moebius_apply_prime hp]
        by_cases hd : p∣q <;> simp [hp.coprime_iff_not_dvd,hd]
      · intro i hi hi0
        have hpow : moebius (p^(i+1))=0 := by
          rw [moebius_apply_prime_pow hp (by omega),if_neg (by omega)]
        simp [coprimeMobiusAF,hpow]
      · simp
    rw [hsum]
    by_cases hd : p∣q <;> simp [coprimeMobiusAF,hd]

lemma coprimeMobiusAF_zeta_eq_primeSupported (q : ℕ) :
    coprimeMobiusAF q*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)=primeSupportedAF q := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((coprimeMobiusAF_multiplicative q).mul isMultiplicative_zeta.natCast) _
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)).mpr
  intro p k hp
  rw [ArithmeticFunction.coe_mul_zeta_apply,Nat.sum_divisors_prime_pow hp,
    coprimeMobiusAF_prime_pow_sum q p k hp]
  by_cases hk : k=0
  · subst k
    simp [primeSupportedAF]
  · simp only [hk,if_false,primeSupportedAF]
    rw [ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),Nat.primeFactors_prime_pow hk hp]
    simp

lemma coprimeMobiusAF_eq_supported_mul_mobius (q : ℕ) :
    coprimeMobiusAF q=primeSupportedAF q*(moebius : ArithmeticFunction ℝ) := by
  rw [←coprimeMobiusAF_zeta_eq_primeSupported,mul_assoc,ArithmeticFunction.coe_zeta_mul_coe_moebius,mul_one]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

lemma primeSupportedAF_apply_positive (q n : ℕ) (hn : 1 ≤ n) :
    primeSupportedAF q n=if (∀ p∈n.primeFactors,p∣q) then 1 else 0 := by
  dsimp [primeSupportedAF]
  rw [ArithmeticFunction.prodPrimeFactors_apply (by omega : n≠0)]
  by_cases h : ∀ p∈n.primeFactors,p∣q
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro p hp
    rw [if_pos (h p hp)]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨p,hp,hpq⟩ := h
    exact Finset.prod_eq_zero hp (if_neg hpq)

lemma coprime_mobius_over_n_supported_pointwise (q n : ℕ) (hn : 1 ≤ n) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0)=
      ∑ d∈n.divisors,if (∀ p∈d.primeFactors,p∣q) then
        (1/(d : ℝ))*(((moebius (n/d) : ℤ) : ℝ)/(n/d : ℕ)) else 0 := by
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (coprimeMobiusAF_eq_supported_mul_mobius q)
  rw [ArithmeticFunction.mul_apply] at he
  change coprimeMobiusAF q n=(∑ x∈n.divisorsAntidiagonal,primeSupportedAF q x.1*((moebius x.2 : ℤ) : ℝ)) at he
  rw [Nat.sum_divisorsAntidiagonal (f:=fun d a => primeSupportedAF q d*((moebius a : ℤ) : ℝ))] at he
  calc
    _=coprimeMobiusAF q n/(n : ℝ) := by
      dsimp [coprimeMobiusAF]
      split_ifs <;> simp
    _=(∑ d∈n.divisors,primeSupportedAF q d*((moebius (n/d) : ℤ) : ℝ))/(n : ℝ) := by rw [he]
    _=_ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hdpos := Nat.pos_of_dvd_of_pos hdvd hn
      rw [primeSupportedAF_apply_positive q d hdpos]
      by_cases h : ∀ p∈d.primeFactors,p∣q
      · rw [if_pos h,if_pos h,one_mul]
        have hncast : (n : ℝ)=(d : ℝ)*(n/d : ℕ) := by exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
        rw [hncast]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      · rw [if_neg h,if_neg h,zero_mul,zero_div]

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
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

theorem coprime_mobius_over_n_supported_partial_sum_complete (q Y : ℕ) :
    (∑ n∈Finset.Icc 1 Y,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0)=
      ∑ d∈Finset.Icc 1 Y,if (∀ p∈d.primeFactors,p∣q) then
        (1/(d : ℝ))*(∑ a∈Finset.Icc 1 (Y/d),((moebius a : ℤ) : ℝ)/(a : ℝ)) else 0 := by
  let F : ℕ→ℕ→ℝ := fun d a => if (∀ p∈d.primeFactors,p∣q) then
    (1/(d : ℝ))*(((moebius a : ℤ) : ℝ)/(a : ℝ)) else 0
  have hpoint (n : ℕ) (hn : n∈Finset.Icc 1 Y) :
      (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0)=
        ∑ d∈n.divisors,F d (n/d) := coprime_mobius_over_n_supported_pointwise q n (Finset.mem_Icc.mp hn).1
  rw [Finset.sum_congr rfl hpoint,finite_positive_divisor_reindex Y F]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : ∀ p∈d.primeFactors,p∣q
  · rw [if_pos h,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact if_pos h
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a ha
    exact if_neg h

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (q Y : ℕ) :
    (∑ n∈Finset.Icc 1 Y,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0)=
      ∑ d∈Finset.Icc 1 Y,if (∀ p∈d.primeFactors,p∣q) then
        (1/(d : ℝ))*(∑ a∈Finset.Icc 1 (Y/d),((moebius a : ℤ) : ℝ)/(a : ℝ)) else 0 := Helfgott.coprime_mobius_over_n_supported_partial_sum_complete q Y

#print axioms solution
