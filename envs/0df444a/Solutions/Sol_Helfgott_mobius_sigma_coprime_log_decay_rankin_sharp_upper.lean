-- Prove2me | solution 1 for Helfgott.mobius_sigma_coprime_log_decay_rankin_sharp_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T03:48:42.52133+00:00
-- url     : https://prove2.me/submissions/fe79c8be-3b85-493e-b247-2bb73f599477

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.SpecialFunctions.Log.Summable

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

noncomputable def mobius_rankin_decay_sharp_mobiusSigmaWeight (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))

lemma mobius_rankin_decay_sharp_mobiusSigmaWeight_mul (d a : ℕ) :
    mobius_rankin_decay_sharp_mobiusSigmaWeight (d*a)=if Nat.Coprime d a then mobius_rankin_decay_sharp_mobiusSigmaWeight d*mobius_rankin_decay_sharp_mobiusSigmaWeight a else 0 := by
  by_cases hc : Nat.Coprime d a
  · rw [if_pos hc]
    have hS : (∏ p∈(d*a).primeFactors,((p : ℝ)+1))=
        (∏ p∈d.primeFactors,((p : ℝ)+1))*(∏ p∈a.primeFactors,((p : ℝ)+1)) := by
      rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
    dsimp [mobius_rankin_decay_sharp_mobiusSigmaWeight]
    rw [isMultiplicative_moebius.map_mul_of_coprime hc,Int.cast_mul,hS]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [if_neg hc]
    have hsf : ¬Squarefree (d*a) := fun h => hc (Nat.coprime_of_squarefree_mul h)
    simp [mobius_rankin_decay_sharp_mobiusSigmaWeight,moebius_eq_zero_of_not_squarefree hsf]

lemma mobius_rankin_decay_sharp_moebius_real_cube_eq_self (d : ℕ) : ((moebius d : ℤ) : ℝ)^3=((moebius d : ℤ) : ℝ) := by
  by_cases hd : moebius d=0
  · rw [hd];norm_num
  · obtain h | h := moebius_ne_zero_iff_eq_or.mp hd <;> rw [h] <;> norm_num

lemma mobius_rankin_decay_sharp_mobiusSigmaWeight_moebius_square (d : ℕ) :
    ((moebius d : ℤ) : ℝ)*(mobius_rankin_decay_sharp_mobiusSigmaWeight d)^2=
      ((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by
  dsimp [mobius_rankin_decay_sharp_mobiusSigmaWeight]
  rw [div_pow]
  calc
    _=((moebius d : ℤ) : ℝ)^3/(∏ p∈d.primeFactors,((p : ℝ)+1))^2 := by ring
    _=_ := by rw [mobius_rankin_decay_sharp_moebius_real_cube_eq_self]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_rankin_decay_sharp_squarefree_mobius_sigma_divisor_product (n : ℕ) (hn : Squarefree n) :
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

lemma mobius_rankin_decay_sharp_mobius_sigma_positive_divisor_convolution (n : ℕ) (hn : 1 ≤ n) :
    mobius_rankin_decay_sharp_mobiusSigmaWeight n=∑ d∈n.divisors,
      if Nat.Coprime (n/d) d then
        (((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))))*
          (((moebius (n/d) : ℤ) : ℝ)/(n/d : ℕ)) else 0 := by
  by_cases hsf : Squarefree n
  · have he := mobius_rankin_decay_sharp_squarefree_mobius_sigma_divisor_product n hsf
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
    dsimp [mobius_rankin_decay_sharp_mobiusSigmaWeight]
    have hnR : (n : ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
    field_simp
  · rw [show mobius_rankin_decay_sharp_mobiusSigmaWeight n=0 by simp [mobius_rankin_decay_sharp_mobiusSigmaWeight,moebius_eq_zero_of_not_squarefree hsf]]
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

theorem mobius_rankin_decay_sharp_finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
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

theorem mobius_rankin_decay_sharp_mobius_sigma_coprime_partial_sum_convolution (q Y : ℕ) :
    (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))))*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then
            ((moebius a : ℤ) : ℝ)/(a : ℝ) else 0) else 0 := by
  let c : ℕ→ℝ := fun d => ((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1)))
  let F : ℕ→ℕ→ℝ := fun d a => if Nat.Coprime (d*a) q ∧ Nat.Coprime a d then c d*(((moebius a : ℤ) : ℝ)/(a : ℝ)) else 0
  have hpoint (r : ℕ) (hr : r∈Finset.Icc 1 Y) :
      (if Nat.Coprime r q then mobius_rankin_decay_sharp_mobiusSigmaWeight r else 0)=∑ d∈r.divisors,F d (r/d) := by
    rw [mobius_rankin_decay_sharp_mobius_sigma_positive_divisor_convolution r (Finset.mem_Icc.mp hr).1]
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
  change (∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then mobius_rankin_decay_sharp_mobiusSigmaWeight r else 0)=_
  rw [Finset.sum_congr rfl hpoint,mobius_rankin_decay_sharp_finite_positive_divisor_reindex Y F]
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

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def mobius_rankin_decay_sharp_coprimeMobiusAF (q : ℕ) : ArithmeticFunction ℝ where
  toFun n := if Nat.Coprime n q then ((moebius n : ℤ) : ℝ) else 0
  map_zero' := by simp

noncomputable def mobius_rankin_decay_sharp_primeSupportedAF (q : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => if p∣q then 1 else 0)

lemma mobius_rankin_decay_sharp_coprimeMobiusAF_multiplicative (q : ℕ) : (mobius_rankin_decay_sharp_coprimeMobiusAF q).IsMultiplicative := by
  refine ⟨by simp [mobius_rankin_decay_sharp_coprimeMobiusAF],?_⟩
  intro m n hmn
  change (if Nat.Coprime (m*n) q then ((moebius (m*n) : ℤ) : ℝ) else 0)=_
  change _=(if Nat.Coprime m q then ((moebius m : ℤ) : ℝ) else 0)*
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ) else 0)
  have hmu : ((moebius (m*n) : ℤ) : ℝ)=((moebius m : ℤ) : ℝ)*((moebius n : ℤ) : ℝ) := by
    exact_mod_cast isMultiplicative_moebius.map_mul_of_coprime hmn
  rw [hmu]
  split_ifs <;> simp_all only [Nat.coprime_mul_iff_left] <;> aesop

lemma mobius_rankin_decay_sharp_coprimeMobiusAF_prime_pow_sum (q p k : ℕ) (hp : Nat.Prime p) :
    (∑ i∈Finset.range (k+1),mobius_rankin_decay_sharp_coprimeMobiusAF q (p^i))=
      if k=0 then 1 else if p∣q then 1 else 0 := by
  cases k with
  | zero => simp [mobius_rankin_decay_sharp_coprimeMobiusAF]
  | succ k =>
    rw [Finset.sum_range_succ']
    have hsum : (∑ i∈Finset.range (k+1),mobius_rankin_decay_sharp_coprimeMobiusAF q (p^(i+1)))=
        if p∣q then 0 else -1 := by
      rw [Finset.sum_eq_single 0]
      · norm_num only [Nat.zero_add,pow_one]
        change (if Nat.Coprime p q then ((moebius p : ℤ) : ℝ) else 0)=_
        rw [moebius_apply_prime hp]
        by_cases hd : p∣q <;> simp [hp.coprime_iff_not_dvd,hd]
      · intro i hi hi0
        have hpow : moebius (p^(i+1))=0 := by
          rw [moebius_apply_prime_pow hp (by omega),if_neg (by omega)]
        simp [mobius_rankin_decay_sharp_coprimeMobiusAF,hpow]
      · simp
    rw [hsum]
    by_cases hd : p∣q <;> simp [mobius_rankin_decay_sharp_coprimeMobiusAF,hd]

lemma mobius_rankin_decay_sharp_coprimeMobiusAF_zeta_eq_primeSupported (q : ℕ) :
    mobius_rankin_decay_sharp_coprimeMobiusAF q*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)=mobius_rankin_decay_sharp_primeSupportedAF q := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((mobius_rankin_decay_sharp_coprimeMobiusAF_multiplicative q).mul isMultiplicative_zeta.natCast) _
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)).mpr
  intro p k hp
  rw [ArithmeticFunction.coe_mul_zeta_apply,Nat.sum_divisors_prime_pow hp,
    mobius_rankin_decay_sharp_coprimeMobiusAF_prime_pow_sum q p k hp]
  by_cases hk : k=0
  · subst k
    simp [mobius_rankin_decay_sharp_primeSupportedAF]
  · simp only [hk,if_false,mobius_rankin_decay_sharp_primeSupportedAF]
    rw [ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),Nat.primeFactors_prime_pow hk hp]
    simp

lemma mobius_rankin_decay_sharp_coprimeMobiusAF_eq_supported_mul_mobius (q : ℕ) :
    mobius_rankin_decay_sharp_coprimeMobiusAF q=mobius_rankin_decay_sharp_primeSupportedAF q*(moebius : ArithmeticFunction ℝ) := by
  rw [←mobius_rankin_decay_sharp_coprimeMobiusAF_zeta_eq_primeSupported,mul_assoc,ArithmeticFunction.coe_zeta_mul_coe_moebius,mul_one]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_rankin_decay_sharp_primeSupportedAF_apply_positive (q n : ℕ) (hn : 1 ≤ n) :
    mobius_rankin_decay_sharp_primeSupportedAF q n=if (∀ p∈n.primeFactors,p∣q) then 1 else 0 := by
  dsimp [mobius_rankin_decay_sharp_primeSupportedAF]
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

lemma mobius_rankin_decay_sharp_coprime_mobius_over_n_supported_pointwise (q n : ℕ) (hn : 1 ≤ n) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0)=
      ∑ d∈n.divisors,if (∀ p∈d.primeFactors,p∣q) then
        (1/(d : ℝ))*(((moebius (n/d) : ℤ) : ℝ)/(n/d : ℕ)) else 0 := by
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (mobius_rankin_decay_sharp_coprimeMobiusAF_eq_supported_mul_mobius q)
  rw [ArithmeticFunction.mul_apply] at he
  change mobius_rankin_decay_sharp_coprimeMobiusAF q n=(∑ x∈n.divisorsAntidiagonal,mobius_rankin_decay_sharp_primeSupportedAF q x.1*((moebius x.2 : ℤ) : ℝ)) at he
  rw [Nat.sum_divisorsAntidiagonal (f:=fun d a => mobius_rankin_decay_sharp_primeSupportedAF q d*((moebius a : ℤ) : ℝ))] at he
  calc
    _=mobius_rankin_decay_sharp_coprimeMobiusAF q n/(n : ℝ) := by
      dsimp [mobius_rankin_decay_sharp_coprimeMobiusAF]
      split_ifs <;> simp
    _=(∑ d∈n.divisors,mobius_rankin_decay_sharp_primeSupportedAF q d*((moebius (n/d) : ℤ) : ℝ))/(n : ℝ) := by rw [he]
    _=_ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hdpos := Nat.pos_of_dvd_of_pos hdvd hn
      rw [mobius_rankin_decay_sharp_primeSupportedAF_apply_positive q d hdpos]
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
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_rankin_decay_sharp_coprime_mobius_over_n_supported_partial_sum (q Y : ℕ) :
    (∑ n∈Finset.Icc 1 Y,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0)=
      ∑ d∈Finset.Icc 1 Y,if (∀ p∈d.primeFactors,p∣q) then
        (1/(d : ℝ))*(∑ a∈Finset.Icc 1 (Y/d),((moebius a : ℤ) : ℝ)/(a : ℝ)) else 0 := by
  let F : ℕ→ℕ→ℝ := fun d a => if (∀ p∈d.primeFactors,p∣q) then
    (1/(d : ℝ))*(((moebius a : ℤ) : ℝ)/(a : ℝ)) else 0
  have hpoint (n : ℕ) (hn : n∈Finset.Icc 1 Y) :
      (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0)=
        ∑ d∈n.divisors,F d (n/d) := mobius_rankin_decay_sharp_coprime_mobius_over_n_supported_pointwise q n (Finset.mem_Icc.mp hn).1
  rw [Finset.sum_congr rfl hpoint,mobius_rankin_decay_sharp_finite_positive_divisor_reindex Y F]
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

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_rankin_decay_sharp_mobius_sigma_product_pos (n : ℕ) : (0:ℝ)<∏ p∈n.primeFactors,((p : ℝ)+1) :=
  Finset.prod_pos (fun p hp => by positivity)

lemma mobius_rankin_decay_sharp_coprime_mobius_reciprocal_majorant (q Y : ℕ) (F : ℕ→ℝ)
    (hF : ∀ N≤Y,|∑ a∈Finset.Icc 1 N,((moebius a : ℤ) : ℝ)/(a : ℝ)|≤F N) :
    |∑ n∈Finset.Icc 1 Y,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0|≤
      ∑ b∈Finset.Icc 1 Y,if (∀ p∈b.primeFactors,p∣q) then (1/(b : ℝ))*F (Y/b) else 0 := by
  rw [mobius_rankin_decay_sharp_coprime_mobius_over_n_supported_partial_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  by_cases hs : ∀ p∈b.primeFactors,p∣q
  · rw [if_pos hs,if_pos hs,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/(b : ℝ))]
    exact mul_le_mul_of_nonneg_left (hF (Y/b) (Nat.div_le_self _ _)) (by positivity)
  · rw [if_neg hs,if_neg hs,abs_zero]

theorem mobius_rankin_decay_sharp_mobius_sigma_coprime_positive_majorant (q Y : ℕ) (F : ℕ→ℝ)
    (hF : ∀ N≤Y,|∑ a∈Finset.Icc 1 N,((moebius a : ℤ) : ℝ)/(a : ℝ)|≤F N) :
    |∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then mobius_rankin_decay_sharp_mobiusSigmaWeight r else 0|≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))))*
          (∑ b∈Finset.Icc 1 (Y/d),if (∀ p∈b.primeFactors,p∣d*q) then
            (1/(b : ℝ))*F ((Y/d)/b) else 0) else 0 := by
  change |∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then
    ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0|≤_
  rw [mobius_rankin_decay_sharp_mobius_sigma_coprime_partial_sum_convolution]
  apply (abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc,if_pos hc,abs_mul]
    have hcoef : (0:ℝ)≤((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))) :=
      div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (mobius_rankin_decay_sharp_mobius_sigma_product_pos d).le)
    rw [abs_of_nonneg hcoef]
    apply mul_le_mul_of_nonneg_left _ hcoef
    exact mobius_rankin_decay_sharp_coprime_mobius_reciprocal_majorant (d*q) (Y/d) F
      (fun N hN => hF N (hN.trans (Nat.div_le_self _ _)))
  · rw [if_neg hc,if_neg hc,abs_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma mobius_rankin_decay_sharp_floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
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

lemma mobius_rankin_decay_sharp_moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem mobius_rankin_decay_sharp_moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
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
  rw [←Finset.sum_filter,he,mobius_rankin_decay_sharp_moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [mobius_rankin_decay_sharp_floorRoot_two_eq_one_iff_squarefree n hn]

lemma mobius_rankin_decay_sharp_coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
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
  rw [←Finset.sum_filter,he,mobius_rankin_decay_sharp_moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem mobius_rankin_decay_sharp_squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast mobius_rankin_decay_sharp_coprime_moebius_divisor_expansion q n hq
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
    exact_mod_cast mobius_rankin_decay_sharp_moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_rankin_decay_sharp_moebius_finite_floor_sum (N : ℕ) (hN : 1≤N) :
    (∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)*(N/d : ℕ))=1 := by
  have hdiv : (∑ n∈Finset.Icc 1 N,∑ d∈n.divisors,((moebius d : ℤ) : ℝ))=1 := by
    have he (n : ℕ) (hn : n∈Finset.Icc 1 N) :
        (∑ d∈n.divisors,((moebius d : ℤ) : ℝ))=if n=1 then (1:ℝ) else 0 := by
      exact_mod_cast mobius_rankin_decay_sharp_moebius_divisor_sum n (by have h:1≤n:=(Finset.mem_Icc.mp hn).1;omega)
    rw [Finset.sum_congr rfl he]
    simp [Finset.mem_Icc,hN]
  have hr := mobius_rankin_decay_sharp_finite_positive_divisor_reindex N (fun d _ => ((moebius d : ℤ) : ℝ))
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

lemma mobius_rankin_decay_sharp_natural_division_fraction_bounds (N d : ℕ) (hd : 1≤d) :
    0≤(N : ℝ)/(d : ℝ)-(N/d : ℕ) ∧ (N : ℝ)/(d : ℝ)-(N/d : ℕ)≤1 := by
  have hdR : (0:ℝ)<(d : ℝ) := by exact_mod_cast hd
  have hlow : ((N/d : ℕ) : ℝ)≤(N : ℝ)/(d : ℝ) := Nat.cast_div_le
  have hupN : N<((N/d)+1)*d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (N/d))
  have hup : (N : ℝ)<(((N/d : ℕ) : ℝ)+1)*(d : ℝ) := by exact_mod_cast hupN
  have hf : (N : ℝ)/(d : ℝ)<((N/d : ℕ) : ℝ)+1 := (div_lt_iff₀ hdR).mpr hup
  constructor <;> linarith

theorem mobius_rankin_decay_sharp_moebius_reciprocal_partial_sum_abs_le_one (N : ℕ) :
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
    rw [mobius_rankin_decay_sharp_moebius_finite_floor_sum N hNp] at hexact
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
      have hf := mobius_rankin_decay_sharp_natural_division_fraction_bounds N d hdpos
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

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_rankin_decay_sharp_natural_power_geometric_series (σ : ℝ) (hσ : 0<σ) (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun k : ℕ => ‖((p^k : ℕ) : ℝ)^(-σ)‖) ∧
      (∑' k : ℕ,((p^k : ℕ) : ℝ)^(-σ))=(1-(p : ℝ)^(-σ))⁻¹ := by
  have hpR : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ)≤p := by positivity
  have he : (fun k : ℕ => ((p^k : ℕ) : ℝ)^(-σ))=(fun k => ((p : ℝ)^(-σ))^k) := by
    funext k
    rw [Nat.cast_pow,←Real.rpow_natCast_mul hp0 k (-σ),mul_comm,Real.rpow_mul_natCast hp0]
  have hr : ‖(p : ℝ)^(-σ)‖<1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hp0 _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  constructor
  · apply (summable_geometric_of_norm_lt_one hr).congr
    intro k
    rw [←congrFun he k,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  · rw [he]
    exact tsum_geometric_of_norm_lt_one hr

theorem mobius_rankin_decay_sharp_prime_supported_dirichlet_series (q : ℕ) (hq : 1≤q) (σ : ℝ) (hσ : 0<σ) :
    let f : ℕ→ℝ := fun n => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0
    Summable f ∧ (∑' n : ℕ,f n)=∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
  let g : ℕ→ℝ := fun n => (n : ℝ)^(-σ)
  have hg1 : g 1=1 := by simp [g]
  have hmul : ∀ {m n},Nat.Coprime m n → g (m*n)=g m*g n := by
    intro m n hmn
    dsimp [g]
    rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hg1 hmul (fun {p} hp => (mobius_rankin_decay_sharp_natural_power_geometric_series σ hσ p hp).1) q.primeFactors
  have hfilter : q.primeFactors.filter Nat.Prime=q.primeFactors := by
    exact Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hvalue : (∏ p∈q.primeFactors with Nat.Prime p,∑' k : ℕ,g (p^k))=
      ∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
    rw [hfilter]
    exact Finset.prod_congr rfl (fun p hp => (mobius_rankin_decay_sharp_natural_power_geometric_series σ hσ p (Nat.prime_of_mem_primeFactors hp)).2)
  have hmem (n : ℕ) : n∈Nat.factoredNumbers q.primeFactors ↔
      n≠0 ∧ (∀ p∈n.primeFactors,p∣q) := by
    rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
    constructor
    · rintro ⟨hn0,hsub⟩
      exact ⟨hn0,fun p hp => Nat.dvd_of_mem_primeFactors (hsub hp)⟩
    · rintro ⟨hn0,hall⟩
      exact ⟨hn0,fun p hp => Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,hall p hp,by omega⟩⟩
  have he : (Nat.factoredNumbers q.primeFactors).indicator g=
      (fun n : ℕ => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0) := by
    funext n
    rw [Set.indicator_apply]
    by_cases hn : n∈Nat.factoredNumbers q.primeFactors
    · rw [if_pos hn,if_pos ((hmem n).mp hn)]
    · rw [if_neg hn,if_neg (fun hh => hn ((hmem n).mpr hh))]
  constructor
  · rw [←he]
    exact summable_subtype_iff_indicator.mp h.1.of_norm
  · rw [←he,←_root_.tsum_subtype]
    exact h.2.tsum_eq.trans hvalue

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real Filter
open scoped BigOperators Topology Classical
namespace Helfgott

theorem mobius_rankin_decay_sharp_real_zeta_euler_hasProd (σ : ℝ) (hσ : 1 < σ) :
    HasProd (fun p : Nat.Primes => (1-(p : ℝ)^(-σ))⁻¹)
      (∑' n : ℕ,(n : ℝ)^(-σ)) := by
  let g : ℕ → ℝ := fun n => (n : ℝ)^(-σ)
  have hg1 : g 1=1 := by simp [g]
  have hg0 : g 0=0 := by simp [g,Real.zero_rpow (by linarith : -σ ≠ 0)]
  have hmul : ∀ {m n},Nat.Coprime m n → g (m*n)=g m*g n := by
    intro m n _
    dsimp [g]
    rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  have hsum : Summable (fun n : ℕ => ‖g n‖) := by
    simpa only [g,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
  have h := EulerProduct.eulerProduct_hasProd hg1 hmul hsum hg0
  have he : (fun p : Nat.Primes => ∑' k : ℕ,g (p^k))=
      (fun p : Nat.Primes => (1-(p : ℝ)^(-σ))⁻¹) := by
    funext p
    exact (mobius_rankin_decay_sharp_natural_power_geometric_series σ (by linarith) p p.property).2
  rw [he] at h
  exact h

lemma mobius_rankin_decay_sharp_real_zeta_sum_pos (σ : ℝ) (hσ : 1 < σ) :
    0 < ∑' n : ℕ,(n : ℝ)^(-σ) := by
  have hsum := Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
  have h := hsum.sum_le_tsum {1} (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))
  norm_num at h
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Helfgott

theorem mobius_rankin_decay_sharp_rankin_single_euler_factor_upper (x y : ℝ) (hx : 0<x) (hxy : x≤y)
    (hy : y<1) (hysq : y^2≤x) :
    1+x*y/((1+x)*(1-y))≤(1-x^3)/((1-x*y)*(1-x*y^2)) := by
  have hy0 : 0≤y := hx.le.trans hxy
  have hx1 : x<1 := hxy.trans_lt hy
  have hxylt : x*y<x := by simpa only [mul_one] using mul_lt_mul_of_pos_left hy hx
  have hxy1 : x*y<1 := hxylt.trans hx1
  have hy2 : y^2<1 := by nlinarith
  have hxysq1 : x*y^2<1 := (show x*y^2<x by simpa only [mul_one] using mul_lt_mul_of_pos_left hy2 hx).trans hx1
  have hden1 : 0<(1+x)*(1-y) := mul_pos (by linarith) (by linarith)
  have hden2 : 0<(1-x*y)*(1-x*y^2) := mul_pos (by linarith) (by linarith)
  have hfactor : (1+x-y)*(1-x*y)*(1-x*y^2)-(1+x)*(1-y)*(1-x^3)=
      (x-y)*(y^2-x)*(x*y-x-1)*x := by ring
  have hneg : x*y-x-1≤0 := by nlinarith
  have hprod : (x-y)*(y^2-x)*(x*y-x-1)*x≤0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) hneg) hx.le
  have he : 1+x*y/((1+x)*(1-y))=(1+x-y)/((1+x)*(1-y)) := by
    field_simp [ne_of_gt (by linarith : (0:ℝ)<1+x),ne_of_gt (by linarith : (0:ℝ)<1-y)] <;> ring
  rw [he]
  apply (div_le_div_iff₀ hden1 hden2).mpr
  nlinarith [hfactor,hprod]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Real
namespace Helfgott

theorem mobius_rankin_decay_sharp_rankin_single_prime_factor_upper (p s : ℝ) (hp : 1<p) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    1+p^(-s-1)/((1+p^(-1:ℝ))*(1-p^(-s)))≤
      (1-p^(-3:ℝ))/((1-p^(-s-1))*(1-p^(-2*s-1))) := by
  have hp0 : 0<p := by linarith
  have hx : 0<p^(-1:ℝ) := Real.rpow_pos_of_pos hp0 _
  have hxy : p^(-1:ℝ)≤p^(-s) := Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
  have hy : p^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hysq : (p^(-s))^2≤p^(-1:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2]
    exact Real.rpow_le_rpow_of_exponent_le hp.le (by norm_num;linarith)
  have h := mobius_rankin_decay_sharp_rankin_single_euler_factor_upper (p^(-1:ℝ)) (p^(-s)) hx hxy hy hysq
  have he1 : p^(-1:ℝ)*p^(-s)=p^(-s-1) := by
    rw [←Real.rpow_add hp0]
    congr 1
    ring
  have he2 : p^(-1:ℝ)*(p^(-s))^2=p^(-2*s-1) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2,←Real.rpow_add hp0]
    congr 1
    ring
  have he3 : (p^(-1:ℝ))^3=p^(-3:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-1) 3]
    norm_num
  simpa only [he1,he2,he3] using h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Finset Nat Real Filter
open scoped BigOperators Topology Classical
namespace Helfgott

lemma mobius_rankin_decay_sharp_rankin_single_comparison_hasProd (s : ℝ) (hs : 1/2 ≤ s) :
    HasProd (fun p : Nat.Primes => (1-(p : ℝ)^(-3:ℝ))/
      ((1-(p : ℝ)^(-s-1))*(1-(p : ℝ)^(-2*s-1))))
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1))/
        (∑' n : ℕ,(n : ℝ)^(-3:ℝ))) := by
  have h3 := (mobius_rankin_decay_sharp_real_zeta_euler_hasProd 3 (by norm_num)).inv₀ (ne_of_gt (mobius_rankin_decay_sharp_real_zeta_sum_pos 3 (by norm_num)))
  have h1 := mobius_rankin_decay_sharp_real_zeta_euler_hasProd (s+1) (by linarith)
  have h2 := mobius_rankin_decay_sharp_real_zeta_euler_hasProd (2*s+1) (by linarith)
  have h := h3.mul (h1.mul h2)
  have he1 : (fun n : ℕ => (n : ℝ)^(-(s+1)))=(fun n : ℕ => (n : ℝ)^(-s-1)) := by funext n;congr 1;ring
  have he2 : (fun n : ℕ => (n : ℝ)^(-(2*s+1)))=(fun n : ℕ => (n : ℝ)^(-2*s-1)) := by funext n;congr 1;ring
  rw [he1,he2] at h
  have hv : (∑' n : ℕ,(n : ℝ)^(-3:ℝ))⁻¹*((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1))) =
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := by
    rw [div_eq_mul_inv];ring
  rw [hv] at h
  apply h.congr_fun
  intro p
  have e1 : -(s+1)=-s-1 := by ring
  have e2 : -(2*s+1)=-2*s-1 := by ring
  simp only [inv_inv,e1,e2,div_eq_mul_inv,mul_inv_rev]
  ring

theorem mobius_rankin_decay_sharp_rankin_single_finite_prime_product_upper (P : Finset Nat.Primes) (s : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    (∏ p∈P,(1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := by
  let f : Nat.Primes → ℝ := fun p => 1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s)))
  let g : Nat.Primes → ℝ := fun p => (1-(p : ℝ)^(-3:ℝ))/((1-(p : ℝ)^(-s-1))*(1-(p : ℝ)^(-2*s-1)))
  have hf1 (p : Nat.Primes) : 1 ≤ f p := by
    have hp : (1:ℝ)<p := by exact_mod_cast p.property.one_lt
    have hp0 : (0:ℝ)<p := by linarith
    have hy : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    dsimp [f]
    have hd : 0<(1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s)) :=
      mul_pos (by linarith [Real.rpow_pos_of_pos hp0 (-1)]) (by linarith)
    exact le_add_of_nonneg_right (div_nonneg (Real.rpow_nonneg hp0.le _) hd.le)
  have hfg (p : Nat.Primes) : f p ≤ g p :=
    mobius_rankin_decay_sharp_rankin_single_prime_factor_upper (p : ℝ) s (by exact_mod_cast p.property.one_lt) hs0 hs1
  have hg1 (p : Nat.Primes) : 1 ≤ g p := (hf1 p).trans (hfg p)
  have hP : (∏ p∈P,f p) ≤ ∏ p∈P,g p := Finset.prod_le_prod (fun p _ => (by norm_num : (0:ℝ)≤1).trans (hf1 p)) (fun p _ => hfg p)
  apply hP.trans
  apply ge_of_tendsto (mobius_rankin_decay_sharp_rankin_single_comparison_hasProd s hs0)
  exact Filter.eventually_atTop.mpr ⟨P,fun T hPT => Finset.prod_le_prod_of_subset_of_one_le hPT
    (fun p _ => (by norm_num : (0:ℝ)≤1).trans (hg1 p)) (fun p _ _ => hg1 p)⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat
open scoped BigOperators Classical

namespace Helfgott

theorem mobius_rankin_decay_sharp_nonnegative_multiplicative_summable_of_local_product_bound
    (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hfnonneg : ∀ n, 0 ≤ f n)
    (hfmul : ∀ {m n}, Nat.Coprime m n → f (m*n) = f m*f n)
    (hlocal : ∀ {p}, Nat.Prime p → Summable (fun e : ℕ => ‖f (p^e)‖))
    (C : ℝ) (hprod : ∀ s : Finset ℕ,
      (∏ p ∈ s with Nat.Prime p,∑' e : ℕ,f (p^e)) ≤ C) :
    Summable f ∧ (∑' n : ℕ,f n) ≤ C := by
  have hfinite (S : Finset ℕ) : (∑ n ∈ S,f n) ≤ C := by
    let T := S.erase 0
    let P := T.biUnion Nat.primeFactors
    have hmem (n : T) : (n : ℕ) ∈ Nat.factoredNumbers P := by
      apply Nat.mem_factoredNumbers_of_primeFactors_subset
      · exact (Finset.mem_erase.mp n.property).1
      · intro p hp
        exact Finset.mem_biUnion.mpr ⟨n.val,n.property,hp⟩
    let e : T → Nat.factoredNumbers P := fun n => ⟨n.val,hmem n⟩
    have hinj : Function.Injective e := by
      intro n m h
      exact Subtype.ext (congrArg (fun n : Nat.factoredNumbers P => (n : ℕ)) h)
    have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      hf1 hfmul hlocal P
    have hsmall : Summable (fun n : T => f (e n)) := Summable.of_finite
    have hle : (∑ n ∈ T,f n) ≤ ∑' n : Nat.factoredNumbers P,f n := by
      rw [←Finset.sum_coe_sort T f]
      calc
        _ = ∑' n : T,f (e n) := (tsum_fintype _).symm
        _ ≤ _ := Summable.tsum_le_tsum_of_inj e hinj (fun n _ => hfnonneg n)
          (fun _ => le_rfl) hsmall h.1.of_norm
    have hremove : (∑ n ∈ S,f n) = ∑ n ∈ T,f n := by
      dsimp only [T]
      by_cases hzero : 0 ∈ S
      · rw [Finset.sum_erase_eq_sub hzero,hf0,sub_zero]
      · rw [Finset.erase_eq_of_notMem hzero]
    rw [hremove]
    exact hle.trans (h.2.tsum_eq ▸ hprod P)
  exact ⟨summable_of_sum_le hfnonneg hfinite,Real.tsum_le_of_sum_le hfnonneg hfinite⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def mobius_rankin_decay_sharp_rankinSingleMomentWeight (s : ℝ) (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)^2*(n : ℝ)^(-s)/
    (∏ p∈n.primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s)))

lemma mobius_rankin_decay_sharp_rankinSingleMomentWeight_nonneg (s : ℝ) (hs : 0 < s) (n : ℕ) :
    0 ≤ mobius_rankin_decay_sharp_rankinSingleMomentWeight s n := by
  apply div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hy : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  exact mul_nonneg (by positivity) (by linarith)

lemma mobius_rankin_decay_sharp_rankinSingleMomentWeight_mul (s : ℝ) {m n : ℕ} (hc : Nat.Coprime m n) :
    mobius_rankin_decay_sharp_rankinSingleMomentWeight s (m*n)=mobius_rankin_decay_sharp_rankinSingleMomentWeight s m*mobius_rankin_decay_sharp_rankinSingleMomentWeight s n := by
  have hP : (∏ p∈(m*n).primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s)))=
      (∏ p∈m.primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s)))*
      (∏ p∈n.primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s))) := by
    rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
  dsimp [mobius_rankin_decay_sharp_rankinSingleMomentWeight]
  rw [isMultiplicative_moebius.map_mul_of_coprime hc,Int.cast_mul,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity),hP]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_tail (s : ℝ) (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) :
    mobius_rankin_decay_sharp_rankinSingleMomentWeight s (p^k)=0 := by
  have hmu : moebius (p^k)=0 := moebius_eq_zero_of_not_squarefree (by
    rw [squarefree_pow_iff hp.ne_one (by omega)]
    simp only [not_and_or]
    exact Or.inr (by omega))
  simp [mobius_rankin_decay_sharp_rankinSingleMomentWeight,hmu]

lemma mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_series (s : ℝ) (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun k : ℕ => ‖mobius_rankin_decay_sharp_rankinSingleMomentWeight s (p^k)‖) ∧
      (∑' k : ℕ,mobius_rankin_decay_sharp_rankinSingleMomentWeight s (p^k))=
        1+(p : ℝ)^(-s)/(((p : ℝ)+1)*(1-(p : ℝ)^(-s))) := by
  constructor
  · apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro k hk
    rw [mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_tail s p k hp (by simpa only [Finset.mem_range,not_lt] using hk),norm_zero]
  · rw [tsum_eq_sum (s := Finset.range 2) (fun k hk => mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_tail s p k hp (by simpa only [Finset.mem_range,not_lt] using hk))]
    simp [Finset.sum_range_succ,mobius_rankin_decay_sharp_rankinSingleMomentWeight,hp,moebius_apply_prime hp]

lemma mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_rewrite (s : ℝ) (p : ℕ) (hp : Nat.Prime p) :
    1+(p : ℝ)^(-s)/(((p : ℝ)+1)*(1-(p : ℝ)^(-s))) =
      1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s))) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have he : (p : ℝ)^(-s-1)=(p : ℝ)^(-s)/(p : ℝ) := by
    rw [Real.rpow_sub hp0,Real.rpow_one]
  rw [he,Real.rpow_neg_one]
  field_simp <;> ring

theorem mobius_rankin_decay_sharp_rankin_single_moment_bound (s : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    Summable (mobius_rankin_decay_sharp_rankinSingleMomentWeight s) ∧
      (∑' n : ℕ,mobius_rankin_decay_sharp_rankinSingleMomentWeight s n) ≤
        ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := by
  have hs : 0 < s := by linarith
  apply mobius_rankin_decay_sharp_nonnegative_multiplicative_summable_of_local_product_bound (mobius_rankin_decay_sharp_rankinSingleMomentWeight s)
    (by simp [mobius_rankin_decay_sharp_rankinSingleMomentWeight]) (by simp [mobius_rankin_decay_sharp_rankinSingleMomentWeight])
    (mobius_rankin_decay_sharp_rankinSingleMomentWeight_nonneg s hs) (fun {_ _} hc => mobius_rankin_decay_sharp_rankinSingleMomentWeight_mul s hc)
    (fun {p} hp => (mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_series s p hp).1)
  intro S
  have h := mobius_rankin_decay_sharp_rankin_single_finite_prime_product_upper (S.subtype Nat.Prime) s hs0 hs1
  have h' : (∏ p∈S with Nat.Prime p,(1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := by
    exact (Finset.prod_subtype_eq_prod_filter (s := S) (p := Nat.Prime) (fun p : ℕ =>
      (1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s)))))).symm.trans_le h
  calc
    _ = ∏ p∈S with Nat.Prime p,(1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s)))) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [(mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_series s p (Finset.mem_filter.mp hp).2).2]
      exact mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_rewrite s p (Finset.mem_filter.mp hp).2
    _ ≤ _ := h'

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_rankin_decay_sharp_rankin_single_positive_divisor_series_certificate (s : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    let f : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ)^2*(n : ℝ)^(-s)/
      (∏ p∈n.primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s)))
    let C : ℝ := ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/
      (∑' n : ℕ,(n : ℝ)^(-3:ℝ))
    Summable f ∧ (∑' n : ℕ,f n) ≤ C ∧ ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n) ≤ C := by
  dsimp only
  have h := mobius_rankin_decay_sharp_rankin_single_moment_bound s hs0 hs1
  refine ⟨h.1,h.2,?_⟩
  intro Y
  exact (h.1.sum_le_tsum _ (fun n _ => mobius_rankin_decay_sharp_rankinSingleMomentWeight_nonneg s (by linarith) n)).trans h.2

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_rankin_decay_sharp_prime_supported_dirichlet_series_certificate (q : ℕ) (hq : 1≤q) (σ : ℝ) (hσ : 0<σ) :
    let f : ℕ→ℝ := fun n => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0
    Summable f ∧ (∑' n : ℕ,f n)=∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ ∧
      ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n)≤∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
  dsimp only
  have h := mobius_rankin_decay_sharp_prime_supported_dirichlet_series q hq σ hσ
  dsimp only at h
  refine ⟨h.1,h.2,?_⟩
  intro Y
  rw [←h.2]
  exact h.1.sum_le_tsum _ (fun n hn => by split_ifs <;> positivity)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3400000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_rankin_decay_sharp_rankin_positive_coprime_convolution_upper (q Y : ℕ) (hq : 1 ≤ q) (s : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    (∑ e∈Finset.Icc 1 Y,if Nat.Coprime e q then
      (((moebius e : ℤ) : ℝ)^2*(e : ℝ)^(-s)/(∏ p∈e.primeFactors,((p : ℝ)+1)))*
        (∑ b∈Finset.Icc 1 (Y/e),if (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0) else 0) ≤
      (((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)))*
        (∏ p∈q.primeFactors,(1-(p : ℝ)^(-s))⁻¹) := by
  have hs : 0 < s := by linarith
  let F : ℕ → ℝ := fun n => ∏ p∈n.primeFactors,(1-(p : ℝ)^(-s))⁻¹
  have hF : 0 ≤ F q := Finset.prod_nonneg (fun p hp => by
    have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have hpow : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    exact inv_nonneg.mpr (by linarith))
  have heach (e : ℕ) (he : e∈Finset.Icc 1 Y) :
      (if Nat.Coprime e q then
        (((moebius e : ℤ) : ℝ)^2*(e : ℝ)^(-s)/(∏ p∈e.primeFactors,((p : ℝ)+1)))*
          (∑ b∈Finset.Icc 1 (Y/e),if (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0) else 0) ≤
        mobius_rankin_decay_sharp_rankinSingleMomentWeight s e*F q := by
    by_cases hc : Nat.Coprime e q
    · rw [if_pos hc]
      have he0 : 1 ≤ e := (Finset.mem_Icc.mp he).1
      have hser := (mobius_rankin_decay_sharp_prime_supported_dirichlet_series_certificate (e*q) (by nlinarith) s hs).2.2 (Y/e)
      dsimp only at hser
      have hinner : (∑ b∈Finset.Icc 1 (Y/e),if (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0) ≤ F (e*q) := by
        have heq : (∑ b∈Finset.Icc 1 (Y/e),if (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0)=
            ∑ b∈Finset.Icc 1 (Y/e),if b≠0 ∧ (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          have hb0 : b≠0 := by have hh := (Finset.mem_Icc.mp hb).1;omega
          by_cases hsupp : ∀ p∈b.primeFactors,p∣e*q
          · rw [if_pos hsupp,if_pos ⟨hb0,hsupp⟩]
          · rw [if_neg hsupp,if_neg (fun h => hsupp h.2)]
        rw [heq]
        exact hser
      have hmul : F (e*q)=F e*F q := by
        dsimp [F]
        rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
      have hcoef : 0 ≤ ((moebius e : ℤ) : ℝ)^2*(e : ℝ)^(-s)/(∏ p∈e.primeFactors,((p : ℝ)+1)) := by
        exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg e) _))
          (Finset.prod_nonneg (fun _ _ => by positivity))
      calc
        _ ≤ (((moebius e : ℤ) : ℝ)^2*(e : ℝ)^(-s)/(∏ p∈e.primeFactors,((p : ℝ)+1)))*F (e*q) :=
          mul_le_mul_of_nonneg_left hinner hcoef
        _ = mobius_rankin_decay_sharp_rankinSingleMomentWeight s e*F q := by
          rw [hmul]
          dsimp [mobius_rankin_decay_sharp_rankinSingleMomentWeight,F]
          rw [Finset.prod_mul_distrib]
          simp only [div_eq_mul_inv,mul_inv_rev,Finset.prod_inv_distrib]
          ring
    · rw [if_neg hc]
      exact mul_nonneg (mobius_rankin_decay_sharp_rankinSingleMomentWeight_nonneg s hs e) hF
  calc
    _ ≤ ∑ e∈Finset.Icc 1 Y,mobius_rankin_decay_sharp_rankinSingleMomentWeight s e*F q := Finset.sum_le_sum heach
    _ = (∑ e∈Finset.Icc 1 Y,mobius_rankin_decay_sharp_rankinSingleMomentWeight s e)*F q := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((mobius_rankin_decay_sharp_rankin_single_positive_divisor_series_certificate s hs0 hs1).2.2 Y) hF

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def mobius_rankin_decay_sharp_reciprocalAbsPartial (N : ℕ) : ℝ :=
  |∑ a ∈ Icc 1 N, ((moebius a : ℤ) : ℝ) / (a : ℝ)|

noncomputable def mobius_rankin_decay_sharp_mobiusRankinConvolution (q Y : ℕ) (s : ℝ) : ℝ :=
  ∑ e ∈ Icc 1 Y, if Nat.Coprime e q then
    (((moebius e : ℤ) : ℝ)^2 * (e : ℝ)^(-s) /
      (∏ p ∈ e.primeFactors, ((p : ℝ)+1))) *
    (∑ b ∈ Icc 1 (Y/e), if (∀ p ∈ b.primeFactors, p ∣ e*q) then
      (b : ℝ)^(-s) else 0) else 0

noncomputable def mobius_rankin_decay_sharp_mobiusRankinConstant (q : ℕ) (s : ℝ) : ℝ :=
  (((∑' n : ℕ, (n : ℝ)^(-s-1)) * (∑' n : ℕ, (n : ℝ)^(-2*s-1))) /
    (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) *
  (∏ p ∈ q.primeFactors, (1-(p : ℝ)^(-s))⁻¹)

lemma mobius_rankin_decay_sharp_mobius_reciprocal_floor_power_envelope
    (Y L e b : ℕ) (c s : ℝ) (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (he : 1 ≤ e) (hb : 1 ≤ b) (hc : 0 ≤ c) (hs : s ≤ 1)
    (hM : ∀ N : ℕ, L ≤ N → mobius_rankin_decay_sharp_reciprocalAbsPartial N ≤ c) :
    mobius_rankin_decay_sharp_reciprocalAbsPartial ((Y/e)/b) ≤
      c + (((L : ℝ)*e*b/Y)^(1-s)) := by
  by_cases hlo : L ≤ (Y/e)/b
  · exact (hM _ hlo).trans (le_add_of_nonneg_right (by positivity))
  · have hquot : Y/(e*b) < L := by
      rw [← Nat.div_div_eq_div_mul]
      exact lt_of_not_ge hlo
    have hprod : 0 < e*b := Nat.mul_pos he hb
    have hYlt : Y < L*(e*b) := (Nat.div_lt_iff_lt_mul hprod).mp hquot
    have hYp : (0 : ℝ) < Y := by exact_mod_cast hY
    have hbase : 1 ≤ (L : ℝ)*e*b/Y := by
      apply (le_div_iff₀ hYp).mpr
      have hR : (Y : ℝ) < (L : ℝ)*((e*b : ℕ) : ℝ) := by exact_mod_cast hYlt
      push_cast at hR
      nlinarith
    have hp := Real.one_le_rpow hbase (by linarith : 0 ≤ 1-s)
    have hu := mobius_rankin_decay_sharp_moebius_reciprocal_partial_sum_abs_le_one ((Y/e)/b)
    change mobius_rankin_decay_sharp_reciprocalAbsPartial ((Y/e)/b) ≤ 1 at hu
    linarith

lemma mobius_rankin_decay_sharp_mobius_rankin_power_factor (L Y e b sigma mu s : ℝ)
    (hL : 0 ≤ L) (hY : 0 < Y) (he : 0 < e) (hb : 0 < b)
    (hsigma : 0 < sigma) :
    (mu^2/(e*sigma))*(1/b)*((L*e*b/Y)^(1-s)) =
      (L/Y)^(1-s)*(mu^2*e^(-s)/sigma)*b^(-s) := by
  have heq : e^(1-s)/e = e^(-s) := by
    calc
      _ = e^(1-s)/e^(1 : ℝ) := by rw [Real.rpow_one]
      _ = e^((1-s)-1) := (Real.rpow_sub he _ _).symm
      _ = _ := by congr 1; ring
  have hbq : b^(1-s)/b = b^(-s) := by
    calc
      _ = b^(1-s)/b^(1 : ℝ) := by rw [Real.rpow_one]
      _ = b^((1-s)-1) := (Real.rpow_sub hb _ _).symm
      _ = _ := by congr 1; ring
  have hfactor : (L*e*b/Y)^(1-s) = (L/Y)^(1-s)*e^(1-s)*b^(1-s) := by
    rw [show L*e*b/Y = (L/Y*e)*b by ring,
      Real.mul_rpow (by positivity) hb.le, Real.mul_rpow (by positivity) he.le]
  rw [hfactor]
  calc
    _ = (L/Y)^(1-s)*(mu^2/sigma)*(e^(1-s)/e)*(b^(1-s)/b) := by
      field_simp
    _ = _ := by rw [heq,hbq]; ring

theorem mobius_rankin_decay_sharp_mobius_sigma_coprime_rankin_decay_upper
    (q Y L : ℕ) (c s : ℝ) (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (hc : 0 ≤ c) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (hM : ∀ N : ℕ, L ≤ N →
      |∑ a ∈ Icc 1 N, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ c) :
    |∑ r ∈ Icc 1 Y, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p ∈ r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      c*mobius_rankin_decay_sharp_mobiusRankinConstant q 1 +
        ((L : ℝ)/Y)^(1-s)*mobius_rankin_decay_sharp_mobiusRankinConstant q s := by
  have hmajor := mobius_rankin_decay_sharp_mobius_sigma_coprime_positive_majorant q Y mobius_rankin_decay_sharp_reciprocalAbsPartial
    (fun _ _ => le_rfl)
  let P : ℝ := ((L : ℝ)/Y)^(1-s)
  have hP : 0 ≤ P := by positivity
  have hconv :
      (∑ e ∈ Icc 1 Y, if Nat.Coprime e q then
        (((moebius e : ℤ) : ℝ)^2 /
          ((e : ℝ)*(∏ p ∈ e.primeFactors, ((p : ℝ)+1)))) *
        (∑ b ∈ Icc 1 (Y/e), if (∀ p ∈ b.primeFactors, p ∣ e*q) then
          (1/(b : ℝ))*mobius_rankin_decay_sharp_reciprocalAbsPartial ((Y/e)/b) else 0) else 0) ≤
      c*mobius_rankin_decay_sharp_mobiusRankinConvolution q Y 1 + P*mobius_rankin_decay_sharp_mobiusRankinConvolution q Y s := by
    unfold mobius_rankin_decay_sharp_mobiusRankinConvolution
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e heI
    have he : 1 ≤ e := (Finset.mem_Icc.mp heI).1
    have hep : (0 : ℝ) < e := by exact_mod_cast he
    by_cases heq : Nat.Coprime e q
    · simp only [if_pos heq]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b hbI
      have hb : 1 ≤ b := (Finset.mem_Icc.mp hbI).1
      have hbp : (0 : ℝ) < b := by exact_mod_cast hb
      by_cases hsupport : ∀ p ∈ b.primeFactors, p ∣ e*q
      · simp only [if_pos hsupport]
        have hbound := mobius_rankin_decay_sharp_mobius_reciprocal_floor_power_envelope Y L e b c s hY hL
          he hb hc hs1 hM
        have hcoef : 0 ≤ ((moebius e : ℤ) : ℝ)^2 /
            ((e : ℝ)*(∏ p ∈ e.primeFactors, ((p : ℝ)+1))) := by
          positivity
        have hi := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 1/(b : ℝ))) hcoef
        apply hi.trans_eq
        rw [mul_add, mul_add, Real.rpow_neg_one, Real.rpow_neg_one]
        have ht := mobius_rankin_decay_sharp_mobius_rankin_power_factor L Y e b
          (∏ p ∈ e.primeFactors, ((p : ℝ)+1)) ((moebius e : ℤ) : ℝ) s
          (Nat.cast_nonneg L) (by exact_mod_cast hY) hep hbp (mobius_rankin_decay_sharp_mobius_sigma_product_pos e)
        dsimp only [P]
        simp only [mul_assoc] at ht
        simp only [mul_assoc]
        rw [ht]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · simp only [if_neg hsupport, mul_zero, add_zero, le_refl]
    · simp only [if_neg heq, mul_zero, add_zero, le_refl]
  have hfirst : mobius_rankin_decay_sharp_mobiusRankinConvolution q Y 1 ≤ mobius_rankin_decay_sharp_mobiusRankinConstant q 1 :=
    mobius_rankin_decay_sharp_rankin_positive_coprime_convolution_upper q Y hq 1 (by norm_num) (by norm_num)
  have hsecond : mobius_rankin_decay_sharp_mobiusRankinConvolution q Y s ≤ mobius_rankin_decay_sharp_mobiusRankinConstant q s :=
    mobius_rankin_decay_sharp_rankin_positive_coprime_convolution_upper q Y hq s hs0 hs1
  exact hmajor.trans (hconv.trans (add_le_add
    (mul_le_mul_of_nonneg_left hfirst hc) (mul_le_mul_of_nonneg_left hsecond hP)))

theorem mobius_rankin_decay_sharp_mobius_sigma_coprime_log_decay_rankin_upper
    (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a ∈ Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤
        (3/100)/Real.log x)
    (q Y L : ℕ) (s : ℝ) (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 11815 ≤ L)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    let R : ℝ → ℝ := fun t =>
      (((∑' n : ℕ, (n : ℝ)^(-t-1))*(∑' n : ℕ, (n : ℝ)^(-2*t-1)))/
        (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) *
      (∏ p ∈ q.primeFactors, (1-(p : ℝ)^(-t))⁻¹)
    |∑ r ∈ Icc 1 Y, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p ∈ r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      ((3/100)/Real.log (L : ℝ))*R 1 + ((L : ℝ)/Y)^(1-s)*R s := by
  have hLp : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hlogLp : 0 < Real.log (L : ℝ) := Real.log_pos hLp
  apply mobius_rankin_decay_sharp_mobius_sigma_coprime_rankin_decay_upper q Y L ((3/100)/Real.log (L : ℝ))
    s hq hY (by omega) (by positivity) hs0 hs1
  intro N hN
  have hNL : (L : ℝ) ≤ N := by exact_mod_cast hN
  have hNlo : (11815 : ℝ) ≤ N := by exact_mod_cast hL.trans hN
  have hb := hdecay N hNlo
  simp only [Nat.floor_natCast] at hb
  exact hb.trans (div_le_div_of_nonneg_left (by norm_num) hlogLp
    (Real.log_le_log (by linarith) hNL))

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
open Finset Nat
open scoped BigOperators Classical

namespace Helfgott

theorem mobius_rankin_decay_sharp_nonnegative_multiplicative_coprime_sum_mul_local_product_le
    (f : ℕ → ℝ) (hf1 : f 1 = 1) (hfnonneg : ∀ n, 0 ≤ f n)
    (hfmul : ∀ {m n}, Nat.Coprime m n → f (m*n) = f m*f n)
    (hlocal : ∀ {p}, Nat.Prime p → Summable (fun e : ℕ => ‖f (p^e)‖))
    (C : ℝ) (hprod : ∀ P : Finset ℕ,
      (∏ p ∈ P with Nat.Prime p, ∑' e : ℕ, f (p^e)) ≤ C)
    (q Y : ℕ) :
    (∑ n ∈ Icc 1 Y, if Nat.Coprime n q then f n else 0) *
      (∏ p ∈ q.primeFactors, ∑' e : ℕ, f (p^e)) ≤ C := by
  let T := (Icc 1 Y).filter (fun n => Nat.Coprime n q)
  let P := T.biUnion Nat.primeFactors
  have hmem (n : T) : (n : ℕ) ∈ Nat.factoredNumbers P := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset
    · have hn := (Finset.mem_filter.mp n.property).1
      have hn1 := (Finset.mem_Icc.mp hn).1
      omega
    · intro p hp
      exact Finset.mem_biUnion.mpr ⟨n.val, n.property, hp⟩
  let e : T → Nat.factoredNumbers P := fun n => ⟨n.val,hmem n⟩
  have hinj : Function.Injective e := by
    intro n m h
    exact Subtype.ext (congrArg (fun z : Nat.factoredNumbers P => (z : ℕ)) h)
  have hfactored := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hf1 hfmul hlocal P
  have hsmall : Summable (fun n : T => f (e n)) := Summable.of_finite
  have hle : (∑ n ∈ T, f n) ≤
      ∏ p ∈ P with Nat.Prime p, ∑' k : ℕ, f (p^k) := by
    rw [← hfactored.2.tsum_eq, ← Finset.sum_coe_sort T f]
    calc
      _ = ∑' n : T, f (e n) := (tsum_fintype _).symm
      _ ≤ _ := Summable.tsum_le_tsum_of_inj e hinj (fun n _ => hfnonneg n)
        (fun _ => le_rfl) hsmall hfactored.1.of_norm
  have hdisjoint : Disjoint P q.primeFactors := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_biUnion.mp hp with ⟨n, hn, hpn⟩
    have hcop := (Finset.mem_filter.mp hn).2
    exact Finset.disjoint_left.mp hcop.disjoint_primeFactors hpn hq
  have hqfilter : q.primeFactors.filter Nat.Prime = q.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hjoin :
      (∏ p ∈ P with Nat.Prime p, ∑' k : ℕ, f (p^k)) *
        (∏ p ∈ q.primeFactors, ∑' k : ℕ, f (p^k)) =
      ∏ p ∈ P ∪ q.primeFactors with Nat.Prime p, ∑' k : ℕ, f (p^k) := by
    rw [Finset.filter_union, hqfilter,
      Finset.prod_union (hdisjoint.mono (Finset.filter_subset _ _) (by rfl))]
  have hqnonneg : 0 ≤ ∏ p ∈ q.primeFactors, ∑' k : ℕ, f (p^k) :=
    Finset.prod_nonneg (fun p _ => tsum_nonneg (fun k => hfnonneg (p^k)))
  have hT : (∑ n ∈ Icc 1 Y, if Nat.Coprime n q then f n else 0) = ∑ n ∈ T, f n := by
    simp only [T, Finset.sum_filter]
  rw [hT]
  exact (mul_le_mul_of_nonneg_right hle hqnonneg).trans
    (hjoin.symm ▸ hprod (P ∪ q.primeFactors))

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def mobius_rankin_decay_sharp_rankinSingleLocalProduct (q : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ q.primeFactors, (1+(p : ℝ)^(-s)/(((p : ℝ)+1)*(1-(p : ℝ)^(-s))))

noncomputable def mobius_rankin_decay_sharp_rankinSharpCoprimeFactor (q : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s))

lemma mobius_rankin_decay_sharp_rankin_single_local_product_pos (q : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < mobius_rankin_decay_sharp_rankinSingleLocalProduct q s := by
  unfold mobius_rankin_decay_sharp_rankinSingleLocalProduct
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hz : 0 ≤ (p : ℝ)^(-s) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hquot : 0 ≤ (p : ℝ)^(-s)/(((p : ℝ)+1)*(1-(p : ℝ)^(-s))) :=
    div_nonneg hz (by positivity)
  linarith

theorem mobius_rankin_decay_sharp_rankin_single_coprime_moment_upper (q Y : ℕ) (s : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    (∑ n ∈ Icc 1 Y, if Nat.Coprime n q then mobius_rankin_decay_sharp_rankinSingleMomentWeight s n else 0) ≤
      (((∑' n : ℕ, (n : ℝ)^(-s-1))*(∑' n : ℕ, (n : ℝ)^(-2*s-1)))/
        (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) / mobius_rankin_decay_sharp_rankinSingleLocalProduct q s := by
  have hs : 0 < s := by linarith
  apply (le_div_iff₀ (mobius_rankin_decay_sharp_rankin_single_local_product_pos q s hs)).mpr
  have h := mobius_rankin_decay_sharp_nonnegative_multiplicative_coprime_sum_mul_local_product_le
    (mobius_rankin_decay_sharp_rankinSingleMomentWeight s) (by simp [mobius_rankin_decay_sharp_rankinSingleMomentWeight])
    (mobius_rankin_decay_sharp_rankinSingleMomentWeight_nonneg s hs)
    (fun {_ _} hc => mobius_rankin_decay_sharp_rankinSingleMomentWeight_mul s hc)
    (fun {p} hp => (mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_series s p hp).1)
    (((∑' n : ℕ, (n : ℝ)^(-s-1))*(∑' n : ℕ, (n : ℝ)^(-2*s-1)))/
      (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) ?_ q Y
  · have hproduct :
        (∏ p ∈ q.primeFactors, ∑' e : ℕ, mobius_rankin_decay_sharp_rankinSingleMomentWeight s (p^e)) =
          mobius_rankin_decay_sharp_rankinSingleLocalProduct q s := by
      unfold mobius_rankin_decay_sharp_rankinSingleLocalProduct
      apply Finset.prod_congr rfl
      intro p hp
      exact (mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_series s p (Nat.prime_of_mem_primeFactors hp)).2
    simpa only [hproduct] using h
  · intro P
    have hbound := mobius_rankin_decay_sharp_rankin_single_finite_prime_product_upper (P.subtype Nat.Prime) s hs0 hs1
    have hbound' :
        (∏ p ∈ P with Nat.Prime p,
          (1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1 : ℝ))*(1-(p : ℝ)^(-s))))) ≤
        (((∑' n : ℕ, (n : ℝ)^(-s-1))*(∑' n : ℕ, (n : ℝ)^(-2*s-1)))/
          (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) := by
      exact (Finset.prod_subtype_eq_prod_filter (s := P) (p := Nat.Prime) (fun p : ℕ =>
        1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1 : ℝ))*(1-(p : ℝ)^(-s))))).symm.trans_le hbound
    calc
      _ = ∏ p ∈ P with Nat.Prime p,
          (1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1 : ℝ))*(1-(p : ℝ)^(-s)))) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [(mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_series s p (Finset.mem_filter.mp hp).2).2]
        exact mobius_rankin_decay_sharp_rankinSingleMomentWeight_prime_rewrite s p (Finset.mem_filter.mp hp).2
      _ ≤ _ := hbound'

lemma mobius_rankin_decay_sharp_rankin_coprime_local_ratio (q : ℕ) (s : ℝ) (hs : 0 < s) :
    (∏ p ∈ q.primeFactors, (1-(p : ℝ)^(-s))⁻¹) /
      mobius_rankin_decay_sharp_rankinSingleLocalProduct q s = mobius_rankin_decay_sharp_rankinSharpCoprimeFactor q s := by
  unfold mobius_rankin_decay_sharp_rankinSingleLocalProduct mobius_rankin_decay_sharp_rankinSharpCoprimeFactor
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have h1 : 1-(p : ℝ)^(-s) ≠ 0 := by linarith
  have h2 : (p : ℝ)+1 ≠ 0 := by linarith
  have h3 : (p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s) ≠ 0 := by
    have hpositive := mul_pos (by linarith : (0 : ℝ) < p) (by linarith : 0 < 1-(p : ℝ)^(-s))
    nlinarith
  field_simp [h1,h2,h3]
  <;> ring

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_rankin_decay_sharp_rankin_positive_coprime_convolution_sharp_upper (q Y : ℕ) (hq : 1 ≤ q) (s : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    (∑ e∈Finset.Icc 1 Y,if Nat.Coprime e q then
      (((moebius e : ℤ) : ℝ)^2*(e : ℝ)^(-s)/(∏ p∈e.primeFactors,((p : ℝ)+1)))*
        (∑ b∈Finset.Icc 1 (Y/e),if (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0) else 0) ≤
      (((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)))*
        (∏ p∈q.primeFactors,((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s))) := by
  have hs : 0 < s := by linarith
  let F : ℕ → ℝ := fun n => ∏ p∈n.primeFactors,(1-(p : ℝ)^(-s))⁻¹
  have hF : 0 ≤ F q := Finset.prod_nonneg (fun p hp => by
    have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have hpow : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    exact inv_nonneg.mpr (by linarith))
  have heach (e : ℕ) (he : e∈Finset.Icc 1 Y) :
      (if Nat.Coprime e q then
        (((moebius e : ℤ) : ℝ)^2*(e : ℝ)^(-s)/(∏ p∈e.primeFactors,((p : ℝ)+1)))*
          (∑ b∈Finset.Icc 1 (Y/e),if (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0) else 0) ≤
        (if Nat.Coprime e q then mobius_rankin_decay_sharp_rankinSingleMomentWeight s e else 0)*F q := by
    by_cases hc : Nat.Coprime e q
    · rw [if_pos hc]
      have he0 : 1 ≤ e := (Finset.mem_Icc.mp he).1
      have hser := (mobius_rankin_decay_sharp_prime_supported_dirichlet_series_certificate (e*q) (by nlinarith) s hs).2.2 (Y/e)
      dsimp only at hser
      have hinner : (∑ b∈Finset.Icc 1 (Y/e),if (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0) ≤ F (e*q) := by
        have heq : (∑ b∈Finset.Icc 1 (Y/e),if (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0)=
            ∑ b∈Finset.Icc 1 (Y/e),if b≠0 ∧ (∀ p∈b.primeFactors,p∣e*q) then (b : ℝ)^(-s) else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          have hb0 : b≠0 := by have hh := (Finset.mem_Icc.mp hb).1;omega
          by_cases hsupp : ∀ p∈b.primeFactors,p∣e*q
          · rw [if_pos hsupp,if_pos ⟨hb0,hsupp⟩]
          · rw [if_neg hsupp,if_neg (fun h => hsupp h.2)]
        rw [heq]
        exact hser
      have hmul : F (e*q)=F e*F q := by
        dsimp [F]
        rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
      have hcoef : 0 ≤ ((moebius e : ℤ) : ℝ)^2*(e : ℝ)^(-s)/(∏ p∈e.primeFactors,((p : ℝ)+1)) := by
        exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg e) _))
          (Finset.prod_nonneg (fun _ _ => by positivity))
      calc
        _ ≤ (((moebius e : ℤ) : ℝ)^2*(e : ℝ)^(-s)/(∏ p∈e.primeFactors,((p : ℝ)+1)))*F (e*q) :=
          mul_le_mul_of_nonneg_left hinner hcoef
        _ = (if Nat.Coprime e q then mobius_rankin_decay_sharp_rankinSingleMomentWeight s e else 0)*F q := by
          rw [hmul, if_pos hc]
          dsimp [mobius_rankin_decay_sharp_rankinSingleMomentWeight,F]
          rw [Finset.prod_mul_distrib]
          simp only [div_eq_mul_inv,mul_inv_rev,Finset.prod_inv_distrib]
          ring
    · simp only [if_neg hc,zero_mul,le_refl]
  calc
    _ ≤ ∑ e∈Finset.Icc 1 Y,(if Nat.Coprime e q then mobius_rankin_decay_sharp_rankinSingleMomentWeight s e else 0)*F q := Finset.sum_le_sum heach
    _ = (∑ e∈Finset.Icc 1 Y,if Nat.Coprime e q then mobius_rankin_decay_sharp_rankinSingleMomentWeight s e else 0)*F q := by rw [Finset.sum_mul]
    _ ≤ ((((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)))/mobius_rankin_decay_sharp_rankinSingleLocalProduct q s)*F q :=
      mul_le_mul_of_nonneg_right (mobius_rankin_decay_sharp_rankin_single_coprime_moment_upper q Y s hs0 hs1) hF
    _ = _ := by
      change ((((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)))/mobius_rankin_decay_sharp_rankinSingleLocalProduct q s)*
        (∏ p∈q.primeFactors,(1-(p : ℝ)^(-s))⁻¹) =
        (((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)))*mobius_rankin_decay_sharp_rankinSharpCoprimeFactor q s
      rw [← mobius_rankin_decay_sharp_rankin_coprime_local_ratio q s hs]
      ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

noncomputable def mobius_rankin_decay_sharp_mobiusRankinSharpConstant (q : ℕ) (s : ℝ) : ℝ :=
  (((∑' n : ℕ, (n : ℝ)^(-s-1)) * (∑' n : ℕ, (n : ℝ)^(-2*s-1))) /
    (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) *
  (∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s)))

theorem mobius_rankin_decay_sharp_mobius_sigma_coprime_rankin_decay_sharp_upper
    (q Y L : ℕ) (c s : ℝ) (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (hc : 0 ≤ c) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (hM : ∀ N : ℕ, L ≤ N →
      |∑ a ∈ Icc 1 N, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ c) :
    |∑ r ∈ Icc 1 Y, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p ∈ r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      c*mobius_rankin_decay_sharp_mobiusRankinSharpConstant q 1 +
        ((L : ℝ)/Y)^(1-s)*mobius_rankin_decay_sharp_mobiusRankinSharpConstant q s := by
  have hmajor := mobius_rankin_decay_sharp_mobius_sigma_coprime_positive_majorant q Y mobius_rankin_decay_sharp_reciprocalAbsPartial
    (fun _ _ => le_rfl)
  let P : ℝ := ((L : ℝ)/Y)^(1-s)
  have hP : 0 ≤ P := by positivity
  have hconv :
      (∑ e ∈ Icc 1 Y, if Nat.Coprime e q then
        (((moebius e : ℤ) : ℝ)^2 /
          ((e : ℝ)*(∏ p ∈ e.primeFactors, ((p : ℝ)+1)))) *
        (∑ b ∈ Icc 1 (Y/e), if (∀ p ∈ b.primeFactors, p ∣ e*q) then
          (1/(b : ℝ))*mobius_rankin_decay_sharp_reciprocalAbsPartial ((Y/e)/b) else 0) else 0) ≤
      c*mobius_rankin_decay_sharp_mobiusRankinConvolution q Y 1 + P*mobius_rankin_decay_sharp_mobiusRankinConvolution q Y s := by
    unfold mobius_rankin_decay_sharp_mobiusRankinConvolution
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e heI
    have he : 1 ≤ e := (Finset.mem_Icc.mp heI).1
    have hep : (0 : ℝ) < e := by exact_mod_cast he
    by_cases heq : Nat.Coprime e q
    · simp only [if_pos heq]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b hbI
      have hb : 1 ≤ b := (Finset.mem_Icc.mp hbI).1
      have hbp : (0 : ℝ) < b := by exact_mod_cast hb
      by_cases hsupport : ∀ p ∈ b.primeFactors, p ∣ e*q
      · simp only [if_pos hsupport]
        have hbound := mobius_rankin_decay_sharp_mobius_reciprocal_floor_power_envelope Y L e b c s hY hL
          he hb hc hs1 hM
        have hcoef : 0 ≤ ((moebius e : ℤ) : ℝ)^2 /
            ((e : ℝ)*(∏ p ∈ e.primeFactors, ((p : ℝ)+1))) := by
          positivity
        have hi := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 1/(b : ℝ))) hcoef
        apply hi.trans_eq
        rw [mul_add, mul_add, Real.rpow_neg_one, Real.rpow_neg_one]
        have ht := mobius_rankin_decay_sharp_mobius_rankin_power_factor L Y e b
          (∏ p ∈ e.primeFactors, ((p : ℝ)+1)) ((moebius e : ℤ) : ℝ) s
          (Nat.cast_nonneg L) (by exact_mod_cast hY) hep hbp (mobius_rankin_decay_sharp_mobius_sigma_product_pos e)
        dsimp only [P]
        simp only [mul_assoc] at ht
        simp only [mul_assoc]
        rw [ht]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · simp only [if_neg hsupport, mul_zero, add_zero, le_refl]
    · simp only [if_neg heq, mul_zero, add_zero, le_refl]
  have hfirst : mobius_rankin_decay_sharp_mobiusRankinConvolution q Y 1 ≤ mobius_rankin_decay_sharp_mobiusRankinSharpConstant q 1 :=
    mobius_rankin_decay_sharp_rankin_positive_coprime_convolution_sharp_upper q Y hq 1 (by norm_num) (by norm_num)
  have hsecond : mobius_rankin_decay_sharp_mobiusRankinConvolution q Y s ≤ mobius_rankin_decay_sharp_mobiusRankinSharpConstant q s :=
    mobius_rankin_decay_sharp_rankin_positive_coprime_convolution_sharp_upper q Y hq s hs0 hs1
  exact hmajor.trans (hconv.trans (add_le_add
    (mul_le_mul_of_nonneg_left hfirst hc) (mul_le_mul_of_nonneg_left hsecond hP)))

theorem mobius_sigma_coprime_log_decay_rankin_sharp_upper_complete
    (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a ∈ Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤
        (3/100)/Real.log x)
    (q Y L : ℕ) (s : ℝ) (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 11815 ≤ L)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    let R : ℝ → ℝ := fun t =>
      (((∑' n : ℕ, (n : ℝ)^(-t-1))*(∑' n : ℕ, (n : ℝ)^(-2*t-1)))/
        (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) *
      (∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-t)))
    |∑ r ∈ Icc 1 Y, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p ∈ r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      ((3/100)/Real.log (L : ℝ))*R 1 + ((L : ℝ)/Y)^(1-s)*R s := by
  have hLp : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hlogLp : 0 < Real.log (L : ℝ) := Real.log_pos hLp
  apply mobius_rankin_decay_sharp_mobius_sigma_coprime_rankin_decay_sharp_upper q Y L ((3/100)/Real.log (L : ℝ))
    s hq hY (by omega) (by positivity) hs0 hs1
  intro N hN
  have hNL : (L : ℝ) ≤ N := by exact_mod_cast hN
  have hNlo : (11815 : ℝ) ≤ N := by exact_mod_cast hL.trans hN
  have hb := hdecay N hNlo
  simp only [Nat.floor_natCast] at hb
  exact hb.trans (div_le_div_of_nonneg_left (by norm_num) hlogLp
    (Real.log_le_log (by linarith) hNL))

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution 
    (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a ∈ Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤
        (3/100)/Real.log x)
    (q Y L : ℕ) (s : ℝ) (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 11815 ≤ L)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    let R : ℝ → ℝ := fun t =>
      (((∑' n : ℕ, (n : ℝ)^(-t-1))*(∑' n : ℕ, (n : ℝ)^(-2*t-1)))/
        (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) *
      (∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-t)))
    |∑ r ∈ Icc 1 Y, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p ∈ r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      ((3/100)/Real.log (L : ℝ))*R 1 + ((L : ℝ)/Y)^(1-s)*R s := Helfgott.mobius_sigma_coprime_log_decay_rankin_sharp_upper_complete hdecay q Y L s hq hY hL hs0 hs1
#print axioms solution
