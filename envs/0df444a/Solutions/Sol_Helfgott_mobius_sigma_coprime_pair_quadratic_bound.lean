-- Prove2me | solution 1 for Helfgott.mobius_sigma_coprime_pair_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T15:43:18.434971+00:00
-- url     : https://prove2.me/submissions/2a606ed9-6c55-4758-b31a-76627eeed545

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt

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
set_option maxHeartbeats 1800000
open Finset Nat
open scoped BigOperators Classical
namespace Helfgott

lemma finite_positive_multiples_reindex (Y d : ℕ) (hd : 1 ≤ d) (F : ℕ→ℝ) :
    (∑ r∈Finset.Icc 1 Y,if d∣r then F r else 0)=∑ a∈Finset.Icc 1 (Y/d),F (d*a) := by
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun r hr => r/d)
  · intro r hr
    obtain ⟨hrI,hrd⟩ := Finset.mem_filter.mp hr
    have hrpos := (Finset.mem_Icc.mp hrI).1
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hrpos hrd) hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hrI).2⟩
  · intro r hr t ht he
    have hrdiv := (Finset.mem_filter.mp hr).2
    have htdiv := (Finset.mem_filter.mp ht).2
    calc r=d*(r/d) := (Nat.mul_div_cancel' hrdiv).symm
         _=d*(t/d) := by rw [he]
         _=t := Nat.mul_div_cancel' htdiv
  · intro a ha
    have hp : 1 ≤ d*a := Nat.mul_pos hd (Finset.mem_Icc.mp ha).1
    have hb : d*a ≤ Y := by
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp (Finset.mem_Icc.mp ha).2
    exact ⟨d*a,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp,hb⟩,dvd_mul_right d a⟩,Nat.mul_div_right a hd⟩
  · intro r hr
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hr).2]

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
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

lemma finite_coprime_pair_mobius_reindex (Y : ℕ) (F : ℕ→ℕ→ℝ) :
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,if Nat.Coprime r t then F r t else 0)=
      ∑ d∈Finset.Icc 1 Y,((moebius d : ℤ) : ℝ)*
        (∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),F (d*a) (d*b)) := by
  have hpoint (r t : ℕ) (hr : 1 ≤ r) :
      (if Nat.Coprime r t then F r t else 0)=
        ∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0 := by
    have hc : (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)=
        if Nat.Coprime r t then (1:ℝ) else 0 := by
      have h := coprime_moebius_divisor_expansion r t (by omega)
      have hR : (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)=
          if Nat.Coprime t r then (1:ℝ) else 0 := by exact_mod_cast h
      simpa only [Nat.coprime_comm] using hR
    calc
      _=(if Nat.Coprime r t then (1:ℝ) else 0)*F r t := by split_ifs <;> simp
      _=(∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ) else 0)*F r t := by rw [hc]
      _=_ := by rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro d hd;split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun t ht => hpoint r t (Finset.mem_Icc.mp hr).1)),Finset.sum_comm]
  have hdiv (t : ℕ) : (∑ r∈Finset.Icc 1 Y,∑ d∈r.divisors,
      if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0)=
      ∑ d∈Finset.Icc 1 Y,∑ a∈Finset.Icc 1 (Y/d),
        if d∣t then ((moebius d : ℤ) : ℝ)*F (d*a) t else 0 := by
    have hr (r : ℕ) (hr : r∈Finset.Icc 1 Y) :
        (∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F r t else 0)=
        ∑ d∈r.divisors,if d∣t then ((moebius d : ℤ) : ℝ)*F (d*(r/d)) t else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [Finset.sum_congr rfl hr,finite_positive_divisor_reindex Y
      (fun d a => if d∣t then ((moebius d : ℤ) : ℝ)*F (d*a) t else 0)]
  rw [Finset.sum_congr rfl (fun t ht => hdiv t),Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [finite_positive_multiples_reindex Y d (Finset.mem_Icc.mp hd).1
    (fun t => ((moebius d : ℤ) : ℝ)*F (d*a) t),Finset.mul_sum]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

noncomputable def mobiusSigmaWeight (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))

lemma mobiusSigmaWeight_mul (d a : ℕ) :
    mobiusSigmaWeight (d*a)=if Nat.Coprime d a then mobiusSigmaWeight d*mobiusSigmaWeight a else 0 := by
  by_cases hc : Nat.Coprime d a
  · rw [if_pos hc]
    have hS : (∏ p∈(d*a).primeFactors,((p : ℝ)+1))=
        (∏ p∈d.primeFactors,((p : ℝ)+1))*(∏ p∈a.primeFactors,((p : ℝ)+1)) := by
      rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
    dsimp [mobiusSigmaWeight]
    rw [isMultiplicative_moebius.map_mul_of_coprime hc,Int.cast_mul,hS]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [if_neg hc]
    have hsf : ¬Squarefree (d*a) := fun h => hc (Nat.coprime_of_squarefree_mul h)
    simp [mobiusSigmaWeight,moebius_eq_zero_of_not_squarefree hsf]

lemma moebius_real_cube_eq_self (d : ℕ) : ((moebius d : ℤ) : ℝ)^3=((moebius d : ℤ) : ℝ) := by
  by_cases hd : moebius d=0
  · rw [hd];norm_num
  · obtain h | h := moebius_ne_zero_iff_eq_or.mp hd <;> rw [h] <;> norm_num

lemma mobiusSigmaWeight_moebius_square (d : ℕ) :
    ((moebius d : ℤ) : ℝ)*(mobiusSigmaWeight d)^2=
      ((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by
  dsimp [mobiusSigmaWeight]
  rw [div_pow]
  calc
    _=((moebius d : ℤ) : ℝ)^3/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by ring
    _=_ := by rw [moebius_real_cube_eq_self]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_sigma_pair_common_divisor (d a b q : ℕ) :
    ((moebius d : ℤ) : ℝ)*
      (if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        mobiusSigmaWeight (d*a)*mobiusSigmaWeight (d*b) else 0)=
      if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then mobiusSigmaWeight a else 0)*
          (if Nat.Coprime b (d*q) then mobiusSigmaWeight b else 0) else 0 := by
  have hfactor := mobiusSigmaWeight_moebius_square d
  rw [mobiusSigmaWeight_mul,mobiusSigmaWeight_mul]
  simp only [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right]
  have hca : Nat.Coprime a d ↔ Nat.Coprime d a := Nat.coprime_comm
  have hcb : Nat.Coprime b d ↔ Nat.Coprime d b := Nat.coprime_comm
  split_ifs <;> simp_all only [hca,hcb,mul_zero,zero_mul] <;> try aesop
  linear_combination (mobiusSigmaWeight a*mobiusSigmaWeight b)*hfactor

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_sigma_coprime_pair_square_decomposition (q Y : ℕ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then f r*f t else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a else 0)^2 else 0 := by
  change (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then mobiusSigmaWeight r*mobiusSigmaWeight t else 0)=_
  have hleft : (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then mobiusSigmaWeight r*mobiusSigmaWeight t else 0)=
      ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,if Nat.Coprime r t then
        (if Nat.Coprime r q ∧ Nat.Coprime t q then mobiusSigmaWeight r*mobiusSigmaWeight t else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> aesop
  rw [hleft,finite_coprime_pair_mobius_reindex]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  have he : (∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),
      ((moebius d : ℤ) : ℝ)*(if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        mobiusSigmaWeight (d*a)*mobiusSigmaWeight (d*b) else 0))=
      ∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),
        if Nat.Coprime d q then (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then mobiusSigmaWeight a else 0)*
          (if Nat.Coprime b (d*q) then mobiusSigmaWeight b else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    exact Finset.sum_congr rfl (fun b hb => mobius_sigma_pair_common_divisor d a b q)
  rw [he]
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc]
    simp only [if_pos hc]
    simp_rw [←Finset.mul_sum]
    rw [←Finset.sum_mul,←Finset.mul_sum]
    change _=(((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
      (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then mobiusSigmaWeight a else 0)^2
    ring
  · simp only [if_neg hc,Finset.sum_const_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_sigma_coprime_pair_quadratic_bound_complete (q Y : ℕ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then f r*f t else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a else 0)^2 else 0 := by
  dsimp only
  rw [mobius_sigma_coprime_pair_square_decomposition]
  apply (abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc,if_pos hc,abs_mul,abs_div,
      abs_of_nonneg (sq_nonneg (∏ p∈d.primeFactors,((p : ℝ)+1))),abs_of_nonneg (sq_nonneg (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then ((moebius a : ℤ) : ℝ)/(∏ p∈a.primeFactors,((p : ℝ)+1)) else 0))]
  · rw [if_neg hc,if_neg hc,abs_zero]

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (q Y : ℕ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then f r*f t else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a else 0)^2 else 0 := Helfgott.mobius_sigma_coprime_pair_quadratic_bound_complete q Y

#print axioms solution
