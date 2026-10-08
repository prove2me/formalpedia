-- Prove2me | solution 1 for Helfgott.mobius_sigma_coprime_partial_sum_convolution
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T15:46:33.331814+00:00
-- url     : https://prove2.me/submissions/d7d657d4-5077-45b3-9cc5-08a726ff8190

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals

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

lemma squarefree_mobius_sigma_divisor_product (n : ℕ) (hn : Squarefree n) :
    (∑ d∈n.divisors,((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1)))=
      (n : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1)) := by
  let f : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (fun p => 1/((p : ℝ)+1))
  have hf : f.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have he := hf.prodPrimeFactors_one_sub_of_squarefree f hn
  have hfd (d : ℕ) (hd : d∈n.divisors) : f d=1/(∏ p∈d.primeFactors,((p : ℝ)+1)) := by
    dsimp [f]
    rw [ArithmeticFunction.prodPrimeFactors_apply ((Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_ne_zero hn.ne_zero)).ne')]
    rw [Finset.prod_div_distrib]
    simp
  have hleft : (∏ p∈n.primeFactors,(1-f p))=(n : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1)) := by
    calc
      _=∏ p∈n.primeFactors,(p : ℝ)/((p : ℝ)+1) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        dsimp [f]
        rw [ArithmeticFunction.prodPrimeFactors_apply hprime.ne_zero,hprime.primeFactors]
        simp only [Finset.prod_singleton]
        have hpos : (0:ℝ)<(p : ℝ)+1 := by positivity
        field_simp
        ring
      _=_ := by rw [Finset.prod_div_distrib,←Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hn]
  rw [hleft] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hfd d hd]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_sigma_positive_divisor_convolution (n : ℕ) (hn : 1 ≤ n) :
    mobiusSigmaWeight n=∑ d∈n.divisors,
      if Nat.Coprime (n/d) d then
        (((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))))*
          (((moebius (n/d) : ℤ) : ℝ)/(n/d : ℕ)) else 0 := by
  by_cases hsf : Squarefree n
  · have he := squarefree_mobius_sigma_divisor_product n hsf
    have hpoint (d : ℕ) (hd : d∈n.divisors) :
        (if Nat.Coprime (n/d) d then
        (((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))))*
          (((moebius (n/d) : ℤ) : ℝ)/(n/d : ℕ)) else 0)=
        (((moebius n : ℤ) : ℝ)/(n : ℝ))*(((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))) := by
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hprod : d*(n/d)=n := Nat.mul_div_cancel' hdvd
      have hsfprod : Squarefree (d*(n/d)) := by rw [hprod];exact hsf
      have hcop : Nat.Coprime (n/d) d := (Nat.coprime_of_squarefree_mul hsfprod).symm
      have hdsf : Squarefree d := hsf.squarefree_of_dvd hdvd
      have hm2 : ((moebius d : ℤ) : ℝ)^2=1 := by exact_mod_cast (by simpa [hdsf] using (moebius_sq (n:=d)))
      have hmul : ((moebius n : ℤ) : ℝ)=((moebius d : ℤ) : ℝ)*((moebius (n/d) : ℤ) : ℝ) := by
        have h := isMultiplicative_moebius.map_mul_of_coprime hcop.symm
        rw [hprod] at h
        exact_mod_cast h
      have hmu : ((moebius (n/d) : ℤ) : ℝ)=((moebius n : ℤ) : ℝ)*((moebius d : ℤ) : ℝ) := by
        calc
          _=1*((moebius (n/d) : ℤ) : ℝ) := by ring
          _=((moebius d : ℤ) : ℝ)^2*((moebius (n/d) : ℤ) : ℝ) := by rw [hm2]
          _=_ := by rw [hmul];ring
      have hncast : (n : ℝ)=(d : ℝ)*(n/d : ℕ) := by exact_mod_cast hprod.symm
      rw [if_pos hcop,hm2,hmu,hncast]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [Finset.sum_congr rfl hpoint,←Finset.mul_sum,he]
    dsimp [mobiusSigmaWeight]
    have hnR : (n : ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
    field_simp
  · rw [show mobiusSigmaWeight n=0 by simp [mobiusSigmaWeight,moebius_eq_zero_of_not_squarefree hsf]]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hc : Nat.Coprime (n/d) d
    · rw [if_pos hc]
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hprod : d*(n/d)=n := Nat.mul_div_cancel' hdvd
      by_cases hdSF : Squarefree d
      · have haSF : ¬Squarefree (n/d) := by
          intro ha
          apply hsf
          rw [←hprod,squarefree_mul hc.symm]
          exact ⟨hdSF,ha⟩
        simp [moebius_eq_zero_of_not_squarefree haSF]
      · simp [moebius_eq_zero_of_not_squarefree hdSF]
    · rw [if_neg hc]

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

theorem mobius_sigma_coprime_partial_sum_convolution_complete (q Y : ℕ) :
    (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))))*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then
            ((moebius a : ℤ) : ℝ)/(a : ℝ) else 0) else 0 := by
  let c : ℕ→ℝ := fun d => ((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1)))
  let F : ℕ→ℕ→ℝ := fun d a => if Nat.Coprime (d*a) q ∧ Nat.Coprime a d then c d*(((moebius a : ℤ) : ℝ)/(a : ℝ)) else 0
  have hpoint (r : ℕ) (hr : r∈Finset.Icc 1 Y) :
      (if Nat.Coprime r q then mobiusSigmaWeight r else 0)=∑ d∈r.divisors,F d (r/d) := by
    rw [mobius_sigma_positive_divisor_convolution r (Finset.mem_Icc.mp hr).1]
    by_cases hc : Nat.Coprime r q
    · rw [if_pos hc]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [F,c]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      by_cases hcd : Nat.Coprime (r/d) d
      · rw [if_pos hcd,if_pos ⟨hc,hcd⟩]
      · rw [if_neg hcd,if_neg (show ¬(Nat.Coprime r q ∧ Nat.Coprime (r/d) d) from by aesop)]
    · rw [if_neg hc]
      symm
      apply Finset.sum_eq_zero
      intro d hd
      dsimp [F]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      simp only [hc,false_and,if_false]
  change (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then mobiusSigmaWeight r else 0)=_
  rw [Finset.sum_congr rfl hpoint,finite_positive_divisor_reindex Y F]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [F,c]
    simp only [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right]
    by_cases ha : Nat.Coprime a q ∧ Nat.Coprime a d
    · have hb : Nat.Coprime a d ∧ Nat.Coprime a q := ⟨ha.2,ha.1⟩
      rw [if_pos ⟨⟨hc,ha.1⟩,ha.2⟩,if_pos hb]
    · have hb : ¬(Nat.Coprime a d ∧ Nat.Coprime a q) := by aesop
      rw [if_neg (show ¬((Nat.Coprime d q ∧ Nat.Coprime a q) ∧ Nat.Coprime a d) from by aesop),if_neg hb,mul_zero]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro a ha
    dsimp [F]
    simp only [Nat.coprime_mul_iff_left,hc,false_and,if_false]

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (q Y : ℕ) :
    (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))))*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then
            ((moebius a : ℤ) : ℝ)/(a : ℝ) else 0) else 0 := Helfgott.mobius_sigma_coprime_partial_sum_convolution_complete q Y

#print axioms solution
