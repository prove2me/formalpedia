-- Prove2me | solution 1 for Helfgott.squarefree_coprime_count_square_root_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T14:25:33.534049+00:00
-- url     : https://prove2.me/submissions/5550a0c3-1904-4175-b32c-925bb2c37850

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Rat.BigOperators

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
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_square_divisor_sum_cap (q n N : ℕ) (hn : 0<n) (hnN : n≤N) :
    (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0 := by
  rw [←Finset.sum_filter,←Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd,hn0⟩,hsq,hcop⟩
    have hdpos : 0<d := Nat.pos_of_dvd_of_pos hd hn
    have hdN : d≤N.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using (Nat.le_of_dvd hn hsq).trans hnN)
    exact ⟨⟨hdpos,hdN⟩,hsq,hcop⟩
  · rintro ⟨⟨hdpos,hdN⟩,hsq,hcop⟩
    exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn.ne'⟩,hsq,hcop⟩

theorem squarefree_coprime_count_exact (q N : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0 := by
  have hp (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
        ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
          if d^2 ∣ n ∧ Nat.Coprime d q ∧ e ∣ n then
            ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ) else 0 := by
    rw [squarefree_coprime_pointwise_expansion q n hq (by have := (Finset.mem_Icc.mp hn).1;omega),
      squarefree_square_divisor_sum_cap q n N (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hs : d^2 ∣ n <;> by_cases hc : Nat.Coprime d q <;> by_cases he : e ∣ n <;>
      simp [hs,hc,he]
  rw [Finset.sum_congr rfl hp,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hde : Nat.Coprime (d^2) e := (hc.pow_left 2).of_dvd_right (Nat.dvd_of_mem_divisors he)
    have hdvd (n : ℕ) : (d^2 ∣ n ∧ Nat.Coprime d q ∧ e ∣ n) ↔ d^2*e ∣ n := by
      constructor
      · rintro ⟨hsq,hc,he⟩
        rw [←hde.lcm_eq_mul]
        exact Nat.lcm_dvd hsq he
      · intro h
        rw [←hde.lcm_eq_mul] at h
        exact ⟨(Nat.lcm_dvd_iff.mp h).1,hc,(Nat.lcm_dvd_iff.mp h).2⟩
    simp_rw [hdvd]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,smul_eq_mul]
    have hi : (Finset.Icc 1 N).filter (fun n => d^2*e ∣ n) =
        (Finset.Ioc 0 N).filter (fun n => d^2*e ∣ n) := by congr 1
    rw [hi,Nat.Ioc_filter_dvd_card_eq_div]
    ring
  · simp [hc]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem finite_divisor_weight_square_energy (M U : ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ) := by
  have hpoint (n : ℕ) : (∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2 =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        if Nat.lcm d e ∣ n then c d*c e else 0 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hdvd : d ∣ n <;> by_cases hevd : e ∣ n <;>
      simp [hdvd,hevd,Nat.lcm_dvd_iff]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,smul_eq_mul]
  have hi : (Finset.Icc 1 M).filter (fun n => Nat.lcm d e ∣ n) =
      (Finset.Ioc 0 M).filter (fun n => Nat.lcm d e ∣ n) := by
    congr 1
  rw [hi,Nat.Ioc_filter_dvd_card_eq_div]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat Real
open scoped BigOperators Classical

namespace Helfgott

lemma nat_div_cast_error_le_one (M k : ℕ) (hk : 0 < k) :
    |((M/k : ℕ) : ℝ)-(M : ℝ)/(k : ℝ)| ≤ 1 := by
  have hlo : ((M/k : ℕ) : ℝ) ≤ (M : ℝ)/(k : ℝ) := Nat.cast_div_le
  have hmod : ((M%k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast Nat.mod_lt M hk
  have he : (k : ℝ)*((M/k : ℕ) : ℝ)+((M%k : ℕ) : ℝ)=(M : ℝ) := by exact_mod_cast Nat.div_add_mod M k
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hupper : (M : ℝ)/(k : ℝ) ≤ ((M/k : ℕ) : ℝ)+1 := (div_le_iff₀ hkR).mpr (by nlinarith)
  linarith

theorem finite_divisor_weight_square_energy_approximation (M U : ℕ) (c : ℕ → ℝ) :
    |(∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ))| ≤
        (∑ d ∈ Finset.Icc 1 U,|c d|)^2 := by
  rw [finite_divisor_weight_square_energy]
  have he : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ))-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 U,|∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,|c d| * |c e| := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro e he
      have hk : 0 < Nat.lcm d e := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
      rw [abs_mul,abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (nat_div_cast_error_le_one M _ hk)
    _ = _ := by rw [pow_two,Finset.sum_mul];apply Finset.sum_congr rfl;intro d hd;rw [Finset.mul_sum]

theorem finite_divisor_weight_leading_quadratic_nonneg (U : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ) := by
  let M := U.factorial
  have hM : (0:ℝ)<M := by exact_mod_cast Nat.factorial_pos U
  have hexact : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ)) =
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hdM : d ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    have heM : e ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp he).2
    rw [Nat.cast_div (Nat.lcm_dvd hdM heM)] <;> try exact_mod_cast (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1).ne'
    ring
  have h := finite_divisor_weight_square_energy M U c
  rw [hexact] at h
  have hnonneg : 0 ≤ (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) :=
    Finset.sum_nonneg (fun n hn => sq_nonneg _)
  rw [h] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg hM

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma moebius_reciprocal_divisor_sum_totient (q : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)/(e : ℝ)) = (q.totient : ℝ)/(q : ℝ) := by
  have hinv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (show ∀ (n : ℕ),n>0 → ∑ i ∈ n.divisors,(i.totient : ℝ) = (n : ℝ) from
      fun n hn => by exact_mod_cast Nat.sum_totient n) q (Nat.pos_of_ne_zero hq)
  rw [Nat.sum_divisorsAntidiagonal (f:=fun x y => ((moebius x : ℤ) : ℝ)*(y : ℝ))] at hinv
  apply (eq_div_iff (show (q : ℝ) ≠ 0 by exact_mod_cast hq)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((q/e : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors he) (by exact_mod_cast he0)]
      ring
    _ = _ := hinv

theorem squarefree_coprime_count_truncated_error (q N : ℕ) (hq : q ≠ 0) :
    |(∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (N : ℝ)*((q.totient : ℝ)/(q : ℝ))*
        (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)| ≤
      (N.sqrt : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|) := by
  rw [squarefree_coprime_count_exact q N hq]
  have herr : (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0)-
      (N : ℝ)*((q.totient : ℝ)/(q : ℝ))*
        (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
        if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ)*
          (((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d : ℝ)^2*(e : ℝ))) else 0 := by
    rw [←moebius_reciprocal_divisor_sum_totient q hq,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : Nat.Coprime d q
    · simp only [if_pos hc,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e he
      ring
    · simp [hc]
  rw [herr]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N.sqrt,|∑ e ∈ q.divisors,
        if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ)*
          (((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d : ℝ)^2*(e : ℝ))) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro e he
      by_cases hc : Nat.Coprime d q
      · rw [if_pos hc,abs_mul,abs_mul]
        have hdpos := (Finset.mem_Icc.mp hd).1
        have hepos := Nat.pos_of_mem_divisors he
        have herr1 : |((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d : ℝ)^2*(e : ℝ))| ≤ 1 := by
          simpa only [Nat.cast_mul,Nat.cast_pow] using nat_div_cast_error_le_one N (d^2*e) (Nat.mul_pos (pow_pos hdpos 2) hepos)
        have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n:=d)
        calc
          _ ≤ (1*|((moebius e : ℤ) : ℝ)|)*1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)) herr1 (abs_nonneg _) (by positivity)
          _ = _ := by ring
      · simp [hc]
    _ = _ := by simp [Finset.sum_const,Nat.card_Icc,smul_eq_mul]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma principal_character_nat_value (q n : ℕ) :
    (1 : DirichletCharacter ℂ q) n = if Nat.Coprime n q then 1 else 0 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hc)
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).mp h))

lemma principal_LSeries_at_two (q : ℕ) (hq : q ≠ 0) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) 2 =
      ((Real.pi : ℂ)^2/6)*∏ p ∈ q.primeFactors,(1-1/(p : ℂ)^2) := by
  letI : NeZero q := ⟨hq⟩
  have h := DirichletCharacter.LSeries_changeLevel (Nat.one_dvd q)
    (1 : DirichletCharacter ℂ 1) (s:=2) (by norm_num)
  rw [DirichletCharacter.changeLevel_one,DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta (by norm_num),riemannZeta_two] at h
  rw [h]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [principal_character_nat_value]
  try simp only [Nat.coprime_one_right,if_true,one_mul]
  rw [Complex.cpow_neg]
  norm_num [Complex.cpow_natCast]

lemma principal_moebius_LSeries_at_two (q : ℕ) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 =
      ((∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) : ℂ) := by
  rw [LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn,principal_character_nat_value]
    norm_num [Complex.cpow_natCast]
    split_ifs <;> push_cast <;> ring

theorem squarefree_coprime_density_series (q : ℕ) (hq : q ≠ 0) :
    (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) =
      (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹ := by
  have h := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ q) (s:=2) (by norm_num)
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) 2 *
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 = 1 at h
  rw [principal_LSeries_at_two q hq,principal_moebius_LSeries_at_two] at h
  have hr : ((Real.pi^2/6)*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)))*
      (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) = 1 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [apply_ite,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_zero] using h
  have hp0 : (∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hsq : (1 : ℝ)<(p : ℝ)^2 := by nlinarith
    have hinv : 1/(p : ℝ)^2 < 1 := (div_lt_one (by positivity)).mpr hsq
    linarith
  rw [Finset.prod_inv_distrib]
  have hpi : Real.pi^2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have hx : (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) =
      1/((Real.pi^2/6)*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2))) := by
    apply (eq_div_iff (mul_ne_zero (div_ne_zero hpi (by norm_num)) hp0)).mpr
    simpa only [mul_comm] using hr
  rw [hx]
  field_simp [hpi,hp0]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma shifted_reciprocal_square_sum_le (D K : ℕ) (hD : 1≤D) :
    (∑ n ∈ Finset.range K,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) := by
  have hpoint (n : ℕ) : 1/((n+D+1 : ℕ) : ℝ)^2 ≤
      1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ) := by
    have hpos : (0 : ℝ)<((n+D : ℕ) : ℝ) := by exact_mod_cast (show 0<n+D by omega)
    push_cast
    field_simp
    nlinarith
  calc
    _ ≤ ∑ n ∈ Finset.range K,(1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ)) := Finset.sum_le_sum (fun n hn => hpoint n)
    _ = 1/(D : ℝ)-1/((K+D : ℕ) : ℝ) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_assoc,add_comm,add_left_comm] using Finset.sum_range_sub' (fun n : ℕ => 1/((n+D : ℕ) : ℝ)) K
    _ ≤ _ := sub_le_self _ (by positivity)

lemma shifted_reciprocal_square_tsum_le (D : ℕ) (hD : 1≤D) :
    (∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun K => shifted_reciprocal_square_sum_le D K hD)

lemma coprime_moebius_reciprocal_square_norm_le (q n : ℕ) :
    ‖(if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)‖ ≤ 1/(n : ℝ)^2 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc,Real.norm_eq_abs,abs_div]
    rw [show |(n : ℝ)^2| = (n : ℝ)^2 from abs_of_nonneg (sq_nonneg _)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one (n:=n)) (sq_nonneg _)
  · rw [if_neg hc,norm_zero]
    positivity

lemma coprime_moebius_reciprocal_square_summable (q : ℕ) :
    Summable (fun n : ℕ => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) := by
  exact Summable.of_norm_bounded hasSum_zeta_two.summable (fun n => coprime_moebius_reciprocal_square_norm_le q n)

lemma reciprocal_square_tsum_le_two : (∑' n : ℕ,1/(n : ℝ)^2) ≤ 2 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at h
  have ht := shifted_reciprocal_square_tsum_le 1 (by norm_num)
  norm_num [add_assoc] at ht
  simp only [one_div]
  linarith

lemma coprime_moebius_density_norm_le_two (q : ℕ) (hq : q ≠ 0) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹| ≤ 2 := by
  rw [←squarefree_coprime_density_series q hq]
  have hf := coprime_moebius_reciprocal_square_summable q
  calc
    _ ≤ ∑' n : ℕ,‖if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ,1/(n : ℝ)^2 := hf.norm.tsum_le_tsum
      (fun n => coprime_moebius_reciprocal_square_norm_le q n) hasSum_zeta_two.summable
    _ ≤ _ := reciprocal_square_tsum_le_two

theorem coprime_moebius_density_tail_error (q D : ℕ) (hq : q ≠ 0) (hD : 1≤D) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹-
      (∑ n ∈ Finset.Icc 1 D,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)| ≤ 1/(D : ℝ) := by
  let f : ℕ → ℝ := fun n => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0
  have hf : Summable f := coprime_moebius_reciprocal_square_summable q
  have hs : (∑ n ∈ Finset.range (D+1),f n) = ∑ n ∈ Finset.Icc 1 D,f n := by
    rw [Finset.range_eq_Ico]
    have he : Finset.Ico 0 (D+1) = insert 0 (Finset.Icc 1 D) := by ext n;simp;omega
    rw [he,Finset.sum_insert (by simp)]
    simp [f]
  rw [←squarefree_coprime_density_series q hq]
  change |(∑' n : ℕ,f n)-(∑ n ∈ Finset.Icc 1 D,f n)| ≤ _
  have he := hf.sum_add_tsum_nat_add (D+1)
  rw [hs] at he
  have herr : (∑' n : ℕ,f n)-(∑ n ∈ Finset.Icc 1 D,f n) = ∑' n : ℕ,f (n+(D+1)) := by linarith
  rw [herr]
  have htail : Summable (fun n : ℕ => f (n+(D+1))) := hf.comp_injective (fun n m h => by omega)
  have hnorm : Summable (fun n : ℕ => 1/((n+D+1 : ℕ) : ℝ)^2) :=
    hasSum_zeta_two.summable.comp_injective (fun n m h => by omega)
  calc
    _ ≤ ∑' n : ℕ,‖f (n+(D+1))‖ := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2 :=
      htail.norm.tsum_le_tsum (fun n => by simpa [f,Nat.add_assoc] using coprime_moebius_reciprocal_square_norm_le q (n+(D+1))) hnorm
    _ ≤ _ := shifted_reciprocal_square_tsum_le D hD

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_coprime_rational_floor_error (q N e : ℕ) (hq : q ≠ 0) (he : 1≤e) :
    |(∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-
      ((N : ℝ)/(e : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)| ≤
      3*Real.sqrt ((N : ℝ)/(e : ℝ)) := by
  let X : ℝ := (N : ℝ)/(e : ℝ)
  let D : ℕ := (N/e).sqrt
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hX : 0≤X := by dsimp [X];positivity
  have heR : (0 : ℝ)<e := by exact_mod_cast he
  have hfloorlo : ((N/e : ℕ) : ℝ) ≤ X := Nat.cast_div_le
  have hfloorhi : X ≤ ((N/e : ℕ) : ℝ)+1 := by
    have h := nat_div_cast_error_le_one N e he
    rw [abs_of_nonpos (sub_nonpos.mpr hfloorlo)] at h
    linarith
  have hDlo : (D : ℝ)^2≤X := (show (D : ℝ)^2 ≤ ((N/e : ℕ) : ℝ) by exact_mod_cast Nat.sqrt_le' (N/e)).trans hfloorlo
  have hDhi : X≤((D : ℝ)+1)^2 := by
    have h : ((N/e : ℕ) : ℝ)+1 ≤ ((D : ℝ)+1)^2 := by
      have hn := Nat.lt_succ_sqrt' (N/e)
      have hn' : N/e+1 ≤ (D+1)^2 := by simpa [D,Nat.succ_eq_add_one] using hn
      exact_mod_cast hn'
    exact hfloorhi.trans h
  have hsqrtlo : (D : ℝ) ≤ Real.sqrt X := by
    have hs := Real.sqrt_sq (show 0≤(D : ℝ) by positivity)
    simpa only [hs] using Real.sqrt_le_sqrt hDlo
  have hsqrthi : Real.sqrt X≤(D : ℝ)+1 := by
    simpa only [Real.sqrt_sq (show 0≤(D : ℝ)+1 by positivity)] using Real.sqrt_le_sqrt hDhi
  have hC : |C|≤2 := coprime_moebius_density_norm_le_two q hq
  change |(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*C|≤3*Real.sqrt X
  by_cases hD0 : D=0
  · rw [hD0]
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ)<1),Finset.sum_empty,zero_sub,abs_neg,abs_mul,abs_of_nonneg hX]
    have hroot1 : Real.sqrt X≤1 := by simpa only [hD0,Nat.cast_zero,zero_add] using hsqrthi
    have hXroot : X≤Real.sqrt X := by nlinarith [Real.sq_sqrt hX,Real.sqrt_nonneg X]
    have hbound : X*|C|≤X*2 := mul_le_mul_of_nonneg_left hC hX
    nlinarith [Real.sqrt_nonneg X]
  · have hD : 1≤D := Nat.pos_of_ne_zero hD0
    have hDR : (0 : ℝ)<D := by exact_mod_cast hD
    have herr : |(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-
        X*(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)|≤(D : ℝ) := by
      rw [Finset.mul_sum,←Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc
        _ ≤ ∑ d ∈ Finset.Icc 1 D,(1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hc : Nat.Coprime d q
          · rw [if_pos hc,if_pos hc]
            have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
            have hr : ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)-X*(((moebius d : ℤ) : ℝ)/(d : ℝ)^2) =
                ((moebius d : ℤ) : ℝ)*(((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d^2*e : ℕ) : ℝ)) := by
              dsimp only [X]
              push_cast
              field_simp <;> ring
            rw [hr,abs_mul]
            have hmu : |((moebius d : ℤ) : ℝ)|≤1 := by exact_mod_cast abs_moebius_le_one (n:=d)
            exact mul_le_one₀ hmu (abs_nonneg _) (nat_div_cast_error_le_one N _ (Nat.mul_pos (pow_pos (Finset.mem_Icc.mp hd).1 2) he))
          · simp [if_neg hc]
        _ = _ := by simp [Nat.card_Icc]
    have htail := coprime_moebius_density_tail_error q D hq hD
    change |C-(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)|≤1/(D : ℝ) at htail
    have hbound : |(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*C|≤(D : ℝ)+X/(D : ℝ) := by
      have heq (S : ℝ) : (∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*C =
          ((∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*S)+X*(S-C) := by ring
      rw [heq (∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)]
      refine (abs_add_le _ _).trans (add_le_add herr ?_)
      rw [abs_mul,abs_of_nonneg hX,abs_sub_comm]
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left htail hX
    refine hbound.trans ?_
    have hrootD : Real.sqrt X≤2*(D : ℝ) := by
      have h1 : (1 : ℝ)≤D := by exact_mod_cast hD
      linarith
    have hxdiv : X/(D : ℝ)≤2*Real.sqrt X := (div_le_iff₀ hDR).mpr (by nlinarith [Real.sq_sqrt hX,Real.sqrt_nonneg X])
    linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_coprime_count_reordered (q N : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*
        (∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0) := by
  rw [squarefree_coprime_count_exact q N hq]
  have hdist : (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
        ((moebius e : ℤ) : ℝ)*(if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [if_pos hc]
      ring
    · simp [if_neg hc]
  rw [hdist,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [←Finset.mul_sum]
  congr 1
  symm
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.sqrt_le_sqrt (Nat.div_le_self N e))⟩
  · intro d hd hnot
    have hdlarge : (N/e).sqrt<d := by
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hnot' : ¬(1≤d ∧ d≤(N/e).sqrt) := by simpa only [Finset.mem_Icc] using hnot
      omega
    have hd2 : N/e<d^2 := Nat.sqrt_lt'.mp hdlarge
    have hdiv : N/(d^2*e)=(N/e)/d^2 := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm]
    rw [hdiv,Nat.div_eq_of_lt hd2]
    simp

lemma squarefree_coprime_density_normalization (q : ℕ) (hq : q ≠ 0) :
    ((q.totient : ℝ)/(q : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹) =
      (6/Real.pi^2)*∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1) := by
  have htot : (q.totient : ℝ)=(q : ℝ)*∏ p ∈ q.primeFactors,(1-(p : ℝ)⁻¹) := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors q)
    push_cast at h
    exact h
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [htot,mul_div_cancel_left₀ _ hqR]
  have hprod : (∏ p ∈ q.primeFactors,(1-(p : ℝ)⁻¹))*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹) =
      ∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
    have hpp : (p : ℝ)+1 ≠ 0 := by linarith
    have hden : 1-1/(p : ℝ)^2 ≠ 0 := by
      have hsq : (1 : ℝ)<(p : ℝ)^2 := by nlinarith
      have hi : 1/(p : ℝ)^2<1 := (div_lt_one (by positivity)).mpr hsq
      linarith
    rw [←div_eq_mul_inv]
    apply (div_eq_iff hden).mpr
    field_simp [hp0,hpp] <;> ring
  calc
    _ = (6/Real.pi^2)*((∏ p ∈ q.primeFactors,(1-(p : ℝ)⁻¹))*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)) := by ring
    _ = _ := by rw [hprod]

theorem squarefree_coprime_count_square_root_error_complete (q N : ℕ) (hq : q ≠ 0) :
    |(∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (N : ℝ)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))| ≤
      3*Real.sqrt (N : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ)) := by
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hmain : (N : ℝ)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1)) =
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N : ℝ)/(e : ℝ))*C := by
    have h := squarefree_coprime_density_normalization q hq
    change ((q.totient : ℝ)/(q : ℝ))*C = _ at h
    rw [mul_assoc,←h,←moebius_reciprocal_divisor_sum_totient q hq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [squarefree_coprime_count_reordered q N hq,hmain,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)*
        (∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-((moebius e : ℤ) : ℝ)*((N : ℝ)/(e : ℝ))*C| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| * (3*Real.sqrt ((N : ℝ)/(e : ℝ))) := by
      apply Finset.sum_le_sum
      intro e he
      have hepos := Nat.pos_of_mem_divisors he
      have herr := squarefree_coprime_rational_floor_error q N e hq hepos
      change |(∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-((N : ℝ)/(e : ℝ))*C| ≤ _ at herr
      rw [mul_assoc,←mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Real.sqrt_div (by positivity)]
      ring

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical

theorem solution  (q N : ℕ) (hq : q ≠ 0) :
    |(∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (N : ℝ)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))| ≤
      3*Real.sqrt (N : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ)) := Helfgott.squarefree_coprime_count_square_root_error_complete q N hq

#print axioms solution
