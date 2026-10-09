-- Prove2me | solution 1 for Helfgott.mobius_sigma_coprime_real_two_power_energy_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T04:45:24.187946+00:00
-- url     : https://prove2.me/submissions/104dadfd-4da1-4c4b-8507-3e8773f7161e

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
import Mathlib.Algebra.Order.Floor.Semifield

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

theorem mobius_sigma_coprime_partial_sum_convolution (q Y : ℕ) :
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
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

theorem coprime_mobius_over_n_supported_partial_sum (q Y : ℕ) :
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

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_sigma_product_pos (n : ℕ) : (0:ℝ)<∏ p∈n.primeFactors,((p : ℝ)+1) :=
  Finset.prod_pos (fun p hp => by positivity)

lemma coprime_mobius_reciprocal_majorant (q Y : ℕ) (F : ℕ→ℝ)
    (hF : ∀ N≤Y,|∑ a∈Finset.Icc 1 N,((moebius a : ℤ) : ℝ)/(a : ℝ)|≤F N) :
    |∑ n∈Finset.Icc 1 Y,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ) else 0|≤
      ∑ b∈Finset.Icc 1 Y,if (∀ p∈b.primeFactors,p∣q) then (1/(b : ℝ))*F (Y/b) else 0 := by
  rw [coprime_mobius_over_n_supported_partial_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  by_cases hs : ∀ p∈b.primeFactors,p∣q
  · rw [if_pos hs,if_pos hs,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/(b : ℝ))]
    exact mul_le_mul_of_nonneg_left (hF (Y/b) (Nat.div_le_self _ _)) (by positivity)
  · rw [if_neg hs,if_neg hs,abs_zero]

theorem mobius_sigma_coprime_positive_majorant (q Y : ℕ) (F : ℕ→ℝ)
    (hF : ∀ N≤Y,|∑ a∈Finset.Icc 1 N,((moebius a : ℤ) : ℝ)/(a : ℝ)|≤F N) :
    |∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then mobiusSigmaWeight r else 0|≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))))*
          (∑ b∈Finset.Icc 1 (Y/d),if (∀ p∈b.primeFactors,p∣d*q) then
            (1/(b : ℝ))*F ((Y/d)/b) else 0) else 0 := by
  change |∑ r∈Finset.Icc 1 Y,if Nat.Coprime r q then
    ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0|≤_
  rw [mobius_sigma_coprime_partial_sum_convolution]
  apply (abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc,if_pos hc,abs_mul]
    have hcoef : (0:ℝ)≤((moebius d : ℤ) : ℝ)^2/((d : ℝ)*(∏ p∈d.primeFactors,((p : ℝ)+1))) :=
      div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (mobius_sigma_product_pos d).le)
    rw [abs_of_nonneg hcoef]
    apply mul_le_mul_of_nonneg_left _ hcoef
    exact coprime_mobius_reciprocal_majorant (d*q) (Y/d) F
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

theorem moebius_reciprocal_partial_sum_abs_le_one (N : ℕ) :
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

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

lemma natural_power_geometric_series (σ : ℝ) (hσ : 0<σ) (p : ℕ) (hp : Nat.Prime p) :
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

theorem prime_supported_dirichlet_series (q : ℕ) (hq : 1≤q) (σ : ℝ) (hσ : 0<σ) :
    let f : ℕ→ℝ := fun n => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0
    Summable f ∧ (∑' n : ℕ,f n)=∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
  let g : ℕ→ℝ := fun n => (n : ℝ)^(-σ)
  have hg1 : g 1=1 := by simp [g]
  have hmul : ∀ {m n},Nat.Coprime m n → g (m*n)=g m*g n := by
    intro m n hmn
    dsimp [g]
    rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hg1 hmul (fun {p} hp => (natural_power_geometric_series σ hσ p hp).1) q.primeFactors
  have hfilter : q.primeFactors.filter Nat.Prime=q.primeFactors := by
    exact Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hvalue : (∏ p∈q.primeFactors with Nat.Prime p,∑' k : ℕ,g (p^k))=
      ∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
    rw [hfilter]
    exact Finset.prod_congr rfl (fun p hp => (natural_power_geometric_series σ hσ p (Nat.prime_of_mem_primeFactors hp)).2)
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

theorem real_zeta_euler_hasProd (σ : ℝ) (hσ : 1 < σ) :
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
    exact (natural_power_geometric_series σ (by linarith) p p.property).2
  rw [he] at h
  exact h

lemma real_zeta_sum_pos (σ : ℝ) (hσ : 1 < σ) :
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

theorem rankin_single_euler_factor_upper (x y : ℝ) (hx : 0<x) (hxy : x≤y)
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

theorem rankin_single_prime_factor_upper (p s : ℝ) (hp : 1<p) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    1+p^(-s-1)/((1+p^(-1:ℝ))*(1-p^(-s)))≤
      (1-p^(-3:ℝ))/((1-p^(-s-1))*(1-p^(-2*s-1))) := by
  have hp0 : 0<p := by linarith
  have hx : 0<p^(-1:ℝ) := Real.rpow_pos_of_pos hp0 _
  have hxy : p^(-1:ℝ)≤p^(-s) := Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
  have hy : p^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hysq : (p^(-s))^2≤p^(-1:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2]
    exact Real.rpow_le_rpow_of_exponent_le hp.le (by norm_num;linarith)
  have h := rankin_single_euler_factor_upper (p^(-1:ℝ)) (p^(-s)) hx hxy hy hysq
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

lemma rankin_single_comparison_hasProd (s : ℝ) (hs : 1/2 ≤ s) :
    HasProd (fun p : Nat.Primes => (1-(p : ℝ)^(-3:ℝ))/
      ((1-(p : ℝ)^(-s-1))*(1-(p : ℝ)^(-2*s-1))))
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1))/
        (∑' n : ℕ,(n : ℝ)^(-3:ℝ))) := by
  have h3 := (real_zeta_euler_hasProd 3 (by norm_num)).inv₀ (ne_of_gt (real_zeta_sum_pos 3 (by norm_num)))
  have h1 := real_zeta_euler_hasProd (s+1) (by linarith)
  have h2 := real_zeta_euler_hasProd (2*s+1) (by linarith)
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

theorem rankin_single_finite_prime_product_upper (P : Finset Nat.Primes) (s : ℝ)
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
    rankin_single_prime_factor_upper (p : ℝ) s (by exact_mod_cast p.property.one_lt) hs0 hs1
  have hg1 (p : Nat.Primes) : 1 ≤ g p := (hf1 p).trans (hfg p)
  have hP : (∏ p∈P,f p) ≤ ∏ p∈P,g p := Finset.prod_le_prod (fun p _ => (by norm_num : (0:ℝ)≤1).trans (hf1 p)) (fun p _ => hfg p)
  apply hP.trans
  apply ge_of_tendsto (rankin_single_comparison_hasProd s hs0)
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

theorem nonnegative_multiplicative_summable_of_local_product_bound
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

noncomputable def rankinSingleMomentWeight (s : ℝ) (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)^2*(n : ℝ)^(-s)/
    (∏ p∈n.primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s)))

lemma rankinSingleMomentWeight_nonneg (s : ℝ) (hs : 0 < s) (n : ℕ) :
    0 ≤ rankinSingleMomentWeight s n := by
  apply div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hy : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  exact mul_nonneg (by positivity) (by linarith)

lemma rankinSingleMomentWeight_mul (s : ℝ) {m n : ℕ} (hc : Nat.Coprime m n) :
    rankinSingleMomentWeight s (m*n)=rankinSingleMomentWeight s m*rankinSingleMomentWeight s n := by
  have hP : (∏ p∈(m*n).primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s)))=
      (∏ p∈m.primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s)))*
      (∏ p∈n.primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s))) := by
    rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
  dsimp [rankinSingleMomentWeight]
  rw [isMultiplicative_moebius.map_mul_of_coprime hc,Int.cast_mul,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity),hP]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma rankinSingleMomentWeight_prime_tail (s : ℝ) (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) :
    rankinSingleMomentWeight s (p^k)=0 := by
  have hmu : moebius (p^k)=0 := moebius_eq_zero_of_not_squarefree (by
    rw [squarefree_pow_iff hp.ne_one (by omega)]
    simp only [not_and_or]
    exact Or.inr (by omega))
  simp [rankinSingleMomentWeight,hmu]

lemma rankinSingleMomentWeight_prime_series (s : ℝ) (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun k : ℕ => ‖rankinSingleMomentWeight s (p^k)‖) ∧
      (∑' k : ℕ,rankinSingleMomentWeight s (p^k))=
        1+(p : ℝ)^(-s)/(((p : ℝ)+1)*(1-(p : ℝ)^(-s))) := by
  constructor
  · apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro k hk
    rw [rankinSingleMomentWeight_prime_tail s p k hp (by simpa only [Finset.mem_range,not_lt] using hk),norm_zero]
  · rw [tsum_eq_sum (s := Finset.range 2) (fun k hk => rankinSingleMomentWeight_prime_tail s p k hp (by simpa only [Finset.mem_range,not_lt] using hk))]
    simp [Finset.sum_range_succ,rankinSingleMomentWeight,hp,moebius_apply_prime hp]

lemma rankinSingleMomentWeight_prime_rewrite (s : ℝ) (p : ℕ) (hp : Nat.Prime p) :
    1+(p : ℝ)^(-s)/(((p : ℝ)+1)*(1-(p : ℝ)^(-s))) =
      1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s))) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have he : (p : ℝ)^(-s-1)=(p : ℝ)^(-s)/(p : ℝ) := by
    rw [Real.rpow_sub hp0,Real.rpow_one]
  rw [he,Real.rpow_neg_one]
  field_simp <;> ring

theorem rankin_single_moment_bound (s : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    Summable (rankinSingleMomentWeight s) ∧
      (∑' n : ℕ,rankinSingleMomentWeight s n) ≤
        ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := by
  have hs : 0 < s := by linarith
  apply nonnegative_multiplicative_summable_of_local_product_bound (rankinSingleMomentWeight s)
    (by simp [rankinSingleMomentWeight]) (by simp [rankinSingleMomentWeight])
    (rankinSingleMomentWeight_nonneg s hs) (fun {_ _} hc => rankinSingleMomentWeight_mul s hc)
    (fun {p} hp => (rankinSingleMomentWeight_prime_series s p hp).1)
  intro S
  have h := rankin_single_finite_prime_product_upper (S.subtype Nat.Prime) s hs0 hs1
  have h' : (∏ p∈S with Nat.Prime p,(1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := by
    exact (Finset.prod_subtype_eq_prod_filter (s := S) (p := Nat.Prime) (fun p : ℕ =>
      (1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s)))))).symm.trans_le h
  calc
    _ = ∏ p∈S with Nat.Prime p,(1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s)))) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [(rankinSingleMomentWeight_prime_series s p (Finset.mem_filter.mp hp).2).2]
      exact rankinSingleMomentWeight_prime_rewrite s p (Finset.mem_filter.mp hp).2
    _ ≤ _ := h'

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

theorem rankin_single_positive_divisor_series_certificate (s : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    let f : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ)^2*(n : ℝ)^(-s)/
      (∏ p∈n.primeFactors,((p : ℝ)+1)*(1-(p : ℝ)^(-s)))
    let C : ℝ := ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/
      (∑' n : ℕ,(n : ℝ)^(-3:ℝ))
    Summable f ∧ (∑' n : ℕ,f n) ≤ C ∧ ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n) ≤ C := by
  dsimp only
  have h := rankin_single_moment_bound s hs0 hs1
  refine ⟨h.1,h.2,?_⟩
  intro Y
  exact (h.1.sum_le_tsum _ (fun n _ => rankinSingleMomentWeight_nonneg s (by linarith) n)).trans h.2

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

theorem prime_supported_dirichlet_series_certificate (q : ℕ) (hq : 1≤q) (σ : ℝ) (hσ : 0<σ) :
    let f : ℕ→ℝ := fun n => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0
    Summable f ∧ (∑' n : ℕ,f n)=∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ ∧
      ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n)≤∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
  dsimp only
  have h := prime_supported_dirichlet_series q hq σ hσ
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

theorem rankin_positive_coprime_convolution_upper (q Y : ℕ) (hq : 1 ≤ q) (s : ℝ)
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
        rankinSingleMomentWeight s e*F q := by
    by_cases hc : Nat.Coprime e q
    · rw [if_pos hc]
      have he0 : 1 ≤ e := (Finset.mem_Icc.mp he).1
      have hser := (prime_supported_dirichlet_series_certificate (e*q) (by nlinarith) s hs).2.2 (Y/e)
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
        _ = rankinSingleMomentWeight s e*F q := by
          rw [hmul]
          dsimp [rankinSingleMomentWeight,F]
          rw [Finset.prod_mul_distrib]
          simp only [div_eq_mul_inv,mul_inv_rev,Finset.prod_inv_distrib]
          ring
    · rw [if_neg hc]
      exact mul_nonneg (rankinSingleMomentWeight_nonneg s hs e) hF
  calc
    _ ≤ ∑ e∈Finset.Icc 1 Y,rankinSingleMomentWeight s e*F q := Finset.sum_le_sum heach
    _ = (∑ e∈Finset.Icc 1 Y,rankinSingleMomentWeight s e)*F q := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((rankin_single_positive_divisor_series_certificate s hs0 hs1).2.2 Y) hF

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def reciprocalAbsPartial (N : ℕ) : ℝ :=
  |∑ a ∈ Icc 1 N, ((moebius a : ℤ) : ℝ) / (a : ℝ)|

noncomputable def mobiusRankinConvolution (q Y : ℕ) (s : ℝ) : ℝ :=
  ∑ e ∈ Icc 1 Y, if Nat.Coprime e q then
    (((moebius e : ℤ) : ℝ)^2 * (e : ℝ)^(-s) /
      (∏ p ∈ e.primeFactors, ((p : ℝ)+1))) *
    (∑ b ∈ Icc 1 (Y/e), if (∀ p ∈ b.primeFactors, p ∣ e*q) then
      (b : ℝ)^(-s) else 0) else 0

noncomputable def mobiusRankinConstant (q : ℕ) (s : ℝ) : ℝ :=
  (((∑' n : ℕ, (n : ℝ)^(-s-1)) * (∑' n : ℕ, (n : ℝ)^(-2*s-1))) /
    (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) *
  (∏ p ∈ q.primeFactors, (1-(p : ℝ)^(-s))⁻¹)

lemma mobius_reciprocal_floor_power_envelope
    (Y L e b : ℕ) (c s : ℝ) (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (he : 1 ≤ e) (hb : 1 ≤ b) (hc : 0 ≤ c) (hs : s ≤ 1)
    (hM : ∀ N : ℕ, L ≤ N → reciprocalAbsPartial N ≤ c) :
    reciprocalAbsPartial ((Y/e)/b) ≤
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
    have hu := moebius_reciprocal_partial_sum_abs_le_one ((Y/e)/b)
    change reciprocalAbsPartial ((Y/e)/b) ≤ 1 at hu
    linarith

lemma mobius_rankin_power_factor (L Y e b sigma mu s : ℝ)
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

theorem mobius_sigma_coprime_rankin_decay_upper
    (q Y L : ℕ) (c s : ℝ) (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (hc : 0 ≤ c) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (hM : ∀ N : ℕ, L ≤ N →
      |∑ a ∈ Icc 1 N, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ c) :
    |∑ r ∈ Icc 1 Y, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p ∈ r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      c*mobiusRankinConstant q 1 +
        ((L : ℝ)/Y)^(1-s)*mobiusRankinConstant q s := by
  have hmajor := mobius_sigma_coprime_positive_majorant q Y reciprocalAbsPartial
    (fun _ _ => le_rfl)
  let P : ℝ := ((L : ℝ)/Y)^(1-s)
  have hP : 0 ≤ P := by positivity
  have hconv :
      (∑ e ∈ Icc 1 Y, if Nat.Coprime e q then
        (((moebius e : ℤ) : ℝ)^2 /
          ((e : ℝ)*(∏ p ∈ e.primeFactors, ((p : ℝ)+1)))) *
        (∑ b ∈ Icc 1 (Y/e), if (∀ p ∈ b.primeFactors, p ∣ e*q) then
          (1/(b : ℝ))*reciprocalAbsPartial ((Y/e)/b) else 0) else 0) ≤
      c*mobiusRankinConvolution q Y 1 + P*mobiusRankinConvolution q Y s := by
    unfold mobiusRankinConvolution
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
        have hbound := mobius_reciprocal_floor_power_envelope Y L e b c s hY hL
          he hb hc hs1 hM
        have hcoef : 0 ≤ ((moebius e : ℤ) : ℝ)^2 /
            ((e : ℝ)*(∏ p ∈ e.primeFactors, ((p : ℝ)+1))) := by
          positivity
        have hi := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 1/(b : ℝ))) hcoef
        apply hi.trans_eq
        rw [mul_add, mul_add, Real.rpow_neg_one, Real.rpow_neg_one]
        have ht := mobius_rankin_power_factor L Y e b
          (∏ p ∈ e.primeFactors, ((p : ℝ)+1)) ((moebius e : ℤ) : ℝ) s
          (Nat.cast_nonneg L) (by exact_mod_cast hY) hep hbp (mobius_sigma_product_pos e)
        dsimp only [P]
        simp only [mul_assoc] at ht
        simp only [mul_assoc]
        rw [ht]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · simp only [if_neg hsupport, mul_zero, add_zero, le_refl]
    · simp only [if_neg heq, mul_zero, add_zero, le_refl]
  have hfirst : mobiusRankinConvolution q Y 1 ≤ mobiusRankinConstant q 1 :=
    rankin_positive_coprime_convolution_upper q Y hq 1 (by norm_num) (by norm_num)
  have hsecond : mobiusRankinConvolution q Y s ≤ mobiusRankinConstant q s :=
    rankin_positive_coprime_convolution_upper q Y hq s hs0 hs1
  exact hmajor.trans (hconv.trans (add_le_add
    (mul_le_mul_of_nonneg_left hfirst hc) (mul_le_mul_of_nonneg_left hsecond hP)))

theorem mobius_sigma_coprime_log_decay_rankin_upper
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
  apply mobius_sigma_coprime_rankin_decay_upper q Y L ((3/100)/Real.log (L : ℝ))
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

theorem nonnegative_multiplicative_coprime_sum_mul_local_product_le
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

noncomputable def rankinSingleLocalProduct (q : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ q.primeFactors, (1+(p : ℝ)^(-s)/(((p : ℝ)+1)*(1-(p : ℝ)^(-s))))

noncomputable def rankinSharpCoprimeFactor (q : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s))

lemma rankin_single_local_product_pos (q : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < rankinSingleLocalProduct q s := by
  unfold rankinSingleLocalProduct
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hz : 0 ≤ (p : ℝ)^(-s) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hquot : 0 ≤ (p : ℝ)^(-s)/(((p : ℝ)+1)*(1-(p : ℝ)^(-s))) :=
    div_nonneg hz (by positivity)
  linarith

theorem rankin_single_coprime_moment_upper (q Y : ℕ) (s : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    (∑ n ∈ Icc 1 Y, if Nat.Coprime n q then rankinSingleMomentWeight s n else 0) ≤
      (((∑' n : ℕ, (n : ℝ)^(-s-1))*(∑' n : ℕ, (n : ℝ)^(-2*s-1)))/
        (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) / rankinSingleLocalProduct q s := by
  have hs : 0 < s := by linarith
  apply (le_div_iff₀ (rankin_single_local_product_pos q s hs)).mpr
  have h := nonnegative_multiplicative_coprime_sum_mul_local_product_le
    (rankinSingleMomentWeight s) (by simp [rankinSingleMomentWeight])
    (rankinSingleMomentWeight_nonneg s hs)
    (fun {_ _} hc => rankinSingleMomentWeight_mul s hc)
    (fun {p} hp => (rankinSingleMomentWeight_prime_series s p hp).1)
    (((∑' n : ℕ, (n : ℝ)^(-s-1))*(∑' n : ℕ, (n : ℝ)^(-2*s-1)))/
      (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) ?_ q Y
  · have hproduct :
        (∏ p ∈ q.primeFactors, ∑' e : ℕ, rankinSingleMomentWeight s (p^e)) =
          rankinSingleLocalProduct q s := by
      unfold rankinSingleLocalProduct
      apply Finset.prod_congr rfl
      intro p hp
      exact (rankinSingleMomentWeight_prime_series s p (Nat.prime_of_mem_primeFactors hp)).2
    simpa only [hproduct] using h
  · intro P
    have hbound := rankin_single_finite_prime_product_upper (P.subtype Nat.Prime) s hs0 hs1
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
        rw [(rankinSingleMomentWeight_prime_series s p (Finset.mem_filter.mp hp).2).2]
        exact rankinSingleMomentWeight_prime_rewrite s p (Finset.mem_filter.mp hp).2
      _ ≤ _ := hbound'

lemma rankin_coprime_local_ratio (q : ℕ) (s : ℝ) (hs : 0 < s) :
    (∏ p ∈ q.primeFactors, (1-(p : ℝ)^(-s))⁻¹) /
      rankinSingleLocalProduct q s = rankinSharpCoprimeFactor q s := by
  unfold rankinSingleLocalProduct rankinSharpCoprimeFactor
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

theorem rankin_positive_coprime_convolution_sharp_upper (q Y : ℕ) (hq : 1 ≤ q) (s : ℝ)
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
        (if Nat.Coprime e q then rankinSingleMomentWeight s e else 0)*F q := by
    by_cases hc : Nat.Coprime e q
    · rw [if_pos hc]
      have he0 : 1 ≤ e := (Finset.mem_Icc.mp he).1
      have hser := (prime_supported_dirichlet_series_certificate (e*q) (by nlinarith) s hs).2.2 (Y/e)
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
        _ = (if Nat.Coprime e q then rankinSingleMomentWeight s e else 0)*F q := by
          rw [hmul, if_pos hc]
          dsimp [rankinSingleMomentWeight,F]
          rw [Finset.prod_mul_distrib]
          simp only [div_eq_mul_inv,mul_inv_rev,Finset.prod_inv_distrib]
          ring
    · simp only [if_neg hc,zero_mul,le_refl]
  calc
    _ ≤ ∑ e∈Finset.Icc 1 Y,(if Nat.Coprime e q then rankinSingleMomentWeight s e else 0)*F q := Finset.sum_le_sum heach
    _ = (∑ e∈Finset.Icc 1 Y,if Nat.Coprime e q then rankinSingleMomentWeight s e else 0)*F q := by rw [Finset.sum_mul]
    _ ≤ ((((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)))/rankinSingleLocalProduct q s)*F q :=
      mul_le_mul_of_nonneg_right (rankin_single_coprime_moment_upper q Y s hs0 hs1) hF
    _ = _ := by
      change ((((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)))/rankinSingleLocalProduct q s)*
        (∏ p∈q.primeFactors,(1-(p : ℝ)^(-s))⁻¹) =
        (((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)))*rankinSharpCoprimeFactor q s
      rw [← rankin_coprime_local_ratio q s hs]
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

noncomputable def mobiusRankinSharpConstant (q : ℕ) (s : ℝ) : ℝ :=
  (((∑' n : ℕ, (n : ℝ)^(-s-1)) * (∑' n : ℕ, (n : ℝ)^(-2*s-1))) /
    (∑' n : ℕ, (n : ℝ)^(-3 : ℝ))) *
  (∏ p ∈ q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s)))

theorem mobius_sigma_coprime_rankin_decay_sharp_upper
    (q Y L : ℕ) (c s : ℝ) (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (hc : 0 ≤ c) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (hM : ∀ N : ℕ, L ≤ N →
      |∑ a ∈ Icc 1 N, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ c) :
    |∑ r ∈ Icc 1 Y, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p ∈ r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      c*mobiusRankinSharpConstant q 1 +
        ((L : ℝ)/Y)^(1-s)*mobiusRankinSharpConstant q s := by
  have hmajor := mobius_sigma_coprime_positive_majorant q Y reciprocalAbsPartial
    (fun _ _ => le_rfl)
  let P : ℝ := ((L : ℝ)/Y)^(1-s)
  have hP : 0 ≤ P := by positivity
  have hconv :
      (∑ e ∈ Icc 1 Y, if Nat.Coprime e q then
        (((moebius e : ℤ) : ℝ)^2 /
          ((e : ℝ)*(∏ p ∈ e.primeFactors, ((p : ℝ)+1)))) *
        (∑ b ∈ Icc 1 (Y/e), if (∀ p ∈ b.primeFactors, p ∣ e*q) then
          (1/(b : ℝ))*reciprocalAbsPartial ((Y/e)/b) else 0) else 0) ≤
      c*mobiusRankinConvolution q Y 1 + P*mobiusRankinConvolution q Y s := by
    unfold mobiusRankinConvolution
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
        have hbound := mobius_reciprocal_floor_power_envelope Y L e b c s hY hL
          he hb hc hs1 hM
        have hcoef : 0 ≤ ((moebius e : ℤ) : ℝ)^2 /
            ((e : ℝ)*(∏ p ∈ e.primeFactors, ((p : ℝ)+1))) := by
          positivity
        have hi := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 1/(b : ℝ))) hcoef
        apply hi.trans_eq
        rw [mul_add, mul_add, Real.rpow_neg_one, Real.rpow_neg_one]
        have ht := mobius_rankin_power_factor L Y e b
          (∏ p ∈ e.primeFactors, ((p : ℝ)+1)) ((moebius e : ℤ) : ℝ) s
          (Nat.cast_nonneg L) (by exact_mod_cast hY) hep hbp (mobius_sigma_product_pos e)
        dsimp only [P]
        simp only [mul_assoc] at ht
        simp only [mul_assoc]
        rw [ht]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · simp only [if_neg hsupport, mul_zero, add_zero, le_refl]
    · simp only [if_neg heq, mul_zero, add_zero, le_refl]
  have hfirst : mobiusRankinConvolution q Y 1 ≤ mobiusRankinSharpConstant q 1 :=
    rankin_positive_coprime_convolution_sharp_upper q Y hq 1 (by norm_num) (by norm_num)
  have hsecond : mobiusRankinConvolution q Y s ≤ mobiusRankinSharpConstant q s :=
    rankin_positive_coprime_convolution_sharp_upper q Y hq s hs0 hs1
  exact hmajor.trans (hconv.trans (add_le_add
    (mul_le_mul_of_nonneg_left hfirst hc) (mul_le_mul_of_nonneg_left hsecond hP)))

theorem mobius_sigma_coprime_log_decay_rankin_sharp_upper
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
  apply mobius_sigma_coprime_rankin_decay_sharp_upper q Y L ((3/100)/Real.log (L : ℝ))
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
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

lemma mobius_real_quotient_range (X : ℝ) (e b : ℕ)
    (hX : 1 ≤ X) (he : 1 ≤ e) (hb : 1 ≤ b) (hbX : b ≤ ⌊X⌋₊/e) :
    1 ≤ X/e/b ∧ X/e/b ≤ X := by
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hnat : b*e ≤ ⌊X⌋₊ := (Nat.le_div_iff_mul_le (by omega)).mp hbX
  have hprod : (e : ℝ)*b ≤ X := by
    have hr : (b : ℝ)*e ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hnat
    have hf := Nat.floor_le (by linarith : 0 ≤ X)
    nlinarith
  have hp1 : (1 : ℝ) ≤ (e : ℝ)*b := by exact_mod_cast Nat.mul_le_mul he hb
  rw [div_div]
  constructor
  · exact (le_div_iff₀ (mul_pos hep hbp)).mpr (by simpa using hprod)
  · apply (div_le_iff₀ (mul_pos hep hbp)).mpr
    nlinarith

theorem mobius_sigma_coprime_real_two_power_rankin_upper
    (q : ℕ) (X L T a b s t : ℝ)
    (hq : 1 ≤ q) (hX : 1 ≤ X) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1)
    (hM : ∀ z : ℝ, 1 ≤ z → z ≤ X →
      |∑ r∈Icc 1 ⌊z⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/z)^(1-s)+b*(T/z)^(1-t)) :
    |∑ r∈Icc 1 ⌊X⌋₊, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      a*(L/X)^(1-s)*mobiusRankinSharpConstant q s +
        b*(T/X)^(1-t)*mobiusRankinSharpConstant q t := by
  let Y := ⌊X⌋₊
  let P := (L/X)^(1-s)
  let Z := (T/X)^(1-t)
  have hXp : 0 < X := by linarith
  have hP : 0 ≤ P := by positivity
  have hZ : 0 ≤ Z := by positivity
  have hmajor := mobius_sigma_coprime_positive_majorant q Y reciprocalAbsPartial (fun _ _ => le_rfl)
  have hconv :
      (∑ e∈Icc 1 Y, if Nat.Coprime e q then
        (((moebius e : ℤ) : ℝ)^2/((e : ℝ)*(∏ p∈e.primeFactors,((p : ℝ)+1)))) *
        (∑ k∈Icc 1 (Y/e), if (∀ p∈k.primeFactors,p∣e*q) then
          (1/(k : ℝ))*reciprocalAbsPartial ((Y/e)/k) else 0) else 0) ≤
      a*P*mobiusRankinConvolution q Y s+b*Z*mobiusRankinConvolution q Y t := by
    unfold mobiusRankinConvolution
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e heI
    have he : 1 ≤ e := (Finset.mem_Icc.mp heI).1
    have hep : (0 : ℝ) < e := by exact_mod_cast he
    by_cases heq : Nat.Coprime e q
    · simp only [if_pos heq]
      simp_rw [Finset.mul_sum]
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k hkI
      have hk : 1 ≤ k := (Finset.mem_Icc.mp hkI).1
      have hkp : (0 : ℝ) < k := by exact_mod_cast hk
      by_cases hsupport : ∀ p∈k.primeFactors,p∣e*q
      · simp only [if_pos hsupport]
        have hz := mobius_real_quotient_range X e k hX he hk (Finset.mem_Icc.mp hkI).2
        have hf : ⌊X/e/k⌋₊=(Y/e)/k := by rw [Nat.floor_div_natCast,Nat.floor_div_natCast]
        have hbound := hM (X/e/k) hz.1 hz.2
        rw [hf] at hbound
        change reciprocalAbsPartial ((Y/e)/k) ≤ a*(L/(X/e/k))^(1-s)+b*(T/(X/e/k))^(1-t) at hbound
        have hcoef : 0 ≤ ((moebius e : ℤ) : ℝ)^2/((e : ℝ)*(∏ p∈e.primeFactors,((p : ℝ)+1))) := by positivity
        have hi := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 1/(k : ℝ))) hcoef
        apply hi.trans_eq
        have hp1 := mobius_rankin_power_factor L X e k
          (∏ p∈e.primeFactors,((p : ℝ)+1)) ((moebius e : ℤ) : ℝ) s hL hXp hep hkp (mobius_sigma_product_pos e)
        have hp2 := mobius_rankin_power_factor T X e k
          (∏ p∈e.primeFactors,((p : ℝ)+1)) ((moebius e : ℤ) : ℝ) t hT hXp hep hkp (mobius_sigma_product_pos e)
        have hlq : L/(X/e/k)=L*e*k/X := by field_simp
        have htq : T/(X/e/k)=T*e*k/X := by field_simp
        rw [hlq,htq]
        dsimp only [P,Z]
        calc
          _ = a*(((moebius e : ℤ) : ℝ)^2/((e : ℝ)*(∏ p∈e.primeFactors,((p : ℝ)+1))))*(1/(k : ℝ))*((L*e*k/X)^(1-s)) +
              b*(((moebius e : ℤ) : ℝ)^2/((e : ℝ)*(∏ p∈e.primeFactors,((p : ℝ)+1))))*(1/(k : ℝ))*((T*e*k/X)^(1-t)) := by ring
          _ = _ := by
            rw [mul_assoc a,mul_assoc a,mul_assoc b,mul_assoc b]
            rw [hp1,hp2]
            ring
      · simp only [if_neg hsupport,mul_zero,add_zero,le_refl]
    · simp only [if_neg heq,mul_zero,add_zero,le_refl]
  have hfirst : mobiusRankinConvolution q Y s ≤ mobiusRankinSharpConstant q s :=
    rankin_positive_coprime_convolution_sharp_upper q Y hq s hs0 hs1
  have hsecond : mobiusRankinConvolution q Y t ≤ mobiusRankinSharpConstant q t :=
    rankin_positive_coprime_convolution_sharp_upper q Y hq t ht0 ht1
  exact hmajor.trans (hconv.trans (add_le_add
    (mul_le_mul_of_nonneg_left hfirst (mul_nonneg ha hP))
    (mul_le_mul_of_nonneg_left hsecond (mul_nonneg hb hZ))))

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000
namespace Helfgott

noncomputable def rankinSparseBlock0_6 (a b : ℝ) : ℝ :=
      a*b^2*(1-b)

theorem rankinSparseBlock0_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock0_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock0_6
  positivity

noncomputable def rankinSparseBlock0_7 (a b : ℝ) : ℝ :=
      a*b*(1-b) +
      a^2*(1-a)*b +
      a*(1-a)*b

theorem rankinSparseBlock0_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock0_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock0_7
  positivity

noncomputable def rankinSparseBlock1_0 (a b : ℝ) : ℝ :=
      b

theorem rankinSparseBlock1_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_0
  positivity

noncomputable def rankinSparseBlock1_1 (a b : ℝ) : ℝ :=
      a

theorem rankinSparseBlock1_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_1
  positivity

noncomputable def rankinSparseBlock1_3 (a b : ℝ) : ℝ :=
      2*a*b +
      b^2*(1-b) +
      a^2*(1-a)

theorem rankinSparseBlock1_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_3
  positivity

noncomputable def rankinSparseBlock1_4 (a b : ℝ) : ℝ :=
      b*(1-b) +
      a*(1-a)

theorem rankinSparseBlock1_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_4
  positivity

noncomputable def rankinSparseBlock1_5 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b*(1-b) +
      2*a*(1-a)*b*(1-b)

theorem rankinSparseBlock1_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_5
  positivity

noncomputable def rankinSparseBlock1_6 (a b : ℝ) : ℝ :=
      a*(1-a)*b^2*(1-b) +
      4*a*b^2*(1-b)

theorem rankinSparseBlock1_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_6
  positivity

noncomputable def rankinSparseBlock1_7 (a b : ℝ) : ℝ :=
      6*a*b*(1-b) +
      5*a^2*(1-a)*b +
      6*a*(1-a)*b

theorem rankinSparseBlock1_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_7
  positivity

noncomputable def rankinSparseBlock2_0 (a b : ℝ) : ℝ :=
      2*b

theorem rankinSparseBlock2_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_0
  positivity

noncomputable def rankinSparseBlock2_1 (a b : ℝ) : ℝ :=
      3*a

theorem rankinSparseBlock2_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_1
  positivity

noncomputable def rankinSparseBlock2_3 (a b : ℝ) : ℝ :=
      10*a*b +
      3*b^2*(1-b) +
      a^2*(1-a)

theorem rankinSparseBlock2_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_3
  positivity

noncomputable def rankinSparseBlock2_4 (a b : ℝ) : ℝ :=
      6*b*(1-b) +
      2*a^2*(1-a) +
      6*a*(1-a)

theorem rankinSparseBlock2_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_4
  positivity

noncomputable def rankinSparseBlock2_5 (a b : ℝ) : ℝ :=
      4*a^2*(1-a)*b*(1-b) +
      11*a*(1-a)*b*(1-b)

theorem rankinSparseBlock2_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_5
  positivity

noncomputable def rankinSparseBlock2_6 (a b : ℝ) : ℝ :=
      5*a*(1-a)*b^2*(1-b) +
      9*a*b^2*(1-b)

theorem rankinSparseBlock2_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_6
  positivity

noncomputable def rankinSparseBlock2_7 (a b : ℝ) : ℝ :=
      a^2*b^4 +
      19*a*b*(1-b) +
      14*a^2*(1-a)*b +
      19*a*(1-a)*b

theorem rankinSparseBlock2_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_7
  positivity

noncomputable def rankinSparseBlock2_8 (a b : ℝ) : ℝ :=
      a^4*b^2

theorem rankinSparseBlock2_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_8
  positivity

noncomputable def rankinSparseBlock2_9 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b^2*(1-b)

theorem rankinSparseBlock2_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_9
  positivity

noncomputable def rankinSparseBlock3_0 (a b : ℝ) : ℝ :=
      6*b

theorem rankinSparseBlock3_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_0
  positivity

noncomputable def rankinSparseBlock3_1 (a b : ℝ) : ℝ :=
      9*a

theorem rankinSparseBlock3_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_1
  positivity

noncomputable def rankinSparseBlock3_3 (a b : ℝ) : ℝ :=
      34*a*b +
      6*b^2*(1-b)

theorem rankinSparseBlock3_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_3
  positivity

noncomputable def rankinSparseBlock3_4 (a b : ℝ) : ℝ :=
      20*b*(1-b) +
      8*a^2*(1-a) +
      20*a*(1-a)

theorem rankinSparseBlock3_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_4
  positivity

noncomputable def rankinSparseBlock3_5 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b^4 +
      a^4*b^2*(1-b) +
      13*a^2*(1-a)*b*(1-b) +
      40*a*(1-a)*b*(1-b) +
      2*a^4*b

theorem rankinSparseBlock3_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_5
  positivity

noncomputable def rankinSparseBlock3_6 (a b : ℝ) : ℝ :=
      18*a*(1-a)*b^2*(1-b) +
      2*a*b^4 +
      12*a*b^2*(1-b)

theorem rankinSparseBlock3_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_6
  positivity

noncomputable def rankinSparseBlock3_7 (a b : ℝ) : ℝ :=
      22*a*b*(1-b) +
      26*a^2*(1-a)*b +
      22*a*(1-a)*b

theorem rankinSparseBlock3_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_7
  positivity

noncomputable def rankinSparseBlock3_8 (a b : ℝ) : ℝ :=
      3*a^2*b^4 +
      4*a^4*b^2 +
      13*a*b*(1-b) +
      13*a*(1-a)*b

theorem rankinSparseBlock3_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_8
  positivity

noncomputable def rankinSparseBlock3_9 (a b : ℝ) : ℝ :=
      6*a^2*(1-a)*b^2*(1-b)

theorem rankinSparseBlock3_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_9
  positivity

noncomputable def rankinSparseBlock4_0 (a b : ℝ) : ℝ :=
      10*b

theorem rankinSparseBlock4_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_0
  positivity

noncomputable def rankinSparseBlock4_1 (a b : ℝ) : ℝ :=
      19*a

theorem rankinSparseBlock4_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_1
  positivity

noncomputable def rankinSparseBlock4_3 (a b : ℝ) : ℝ :=
      73*a*b +
      10*b^2*(1-b)

theorem rankinSparseBlock4_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_3
  positivity

noncomputable def rankinSparseBlock4_4 (a b : ℝ) : ℝ :=
      b^4 +
      50*b*(1-b) +
      a^4 +
      18*a^2*(1-a) +
      50*a*(1-a)

theorem rankinSparseBlock4_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_4
  positivity

noncomputable def rankinSparseBlock4_5 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b^4 +
      2*a^4*b^2*(1-b) +
      20*a^2*(1-a)*b*(1-b) +
      94*a*(1-a)*b*(1-b) +
      3*a^4*b

theorem rankinSparseBlock4_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_5
  positivity

noncomputable def rankinSparseBlock4_6 (a b : ℝ) : ℝ :=
      38*a*(1-a)*b^2*(1-b) +
      8*a*b^4 +
      a*b^2*(1-b) +
      3*a^4*b

theorem rankinSparseBlock4_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_6
  positivity

noncomputable def rankinSparseBlock4_7 (a b : ℝ) : ℝ :=
      9*a*b^2*(1-b) +
      36*a^2*(1-a)*b

theorem rankinSparseBlock4_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_7
  positivity

noncomputable def rankinSparseBlock4_8 (a b : ℝ) : ℝ :=
      a^4*b^3*(1-b) +
      8*a^2*b^4 +
      8*a^4*b^2 +
      43*a*b*(1-b) +
      43*a*(1-a)*b

theorem rankinSparseBlock4_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_8
  positivity

noncomputable def rankinSparseBlock4_9 (a b : ℝ) : ℝ :=
      13*a^2*(1-a)*b^2*(1-b)

theorem rankinSparseBlock4_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_9
  positivity

noncomputable def rankinSparseBlock5_0 (a b : ℝ) : ℝ :=
      18*b

theorem rankinSparseBlock5_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_0
  positivity

noncomputable def rankinSparseBlock5_1 (a b : ℝ) : ℝ :=
      37*a

theorem rankinSparseBlock5_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_1
  positivity

noncomputable def rankinSparseBlock5_3 (a b : ℝ) : ℝ :=
      122*a*b +
      6*b^2*(1-b)

theorem rankinSparseBlock5_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_3
  positivity

noncomputable def rankinSparseBlock5_4 (a b : ℝ) : ℝ :=
      3*b^4 +
      6*b^2*(1-b) +
      45*b*(1-b) +
      3*a^4 +
      30*a^2*(1-a) +
      45*a*(1-a)

theorem rankinSparseBlock5_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_4
  positivity

noncomputable def rankinSparseBlock5_5 (a b : ℝ) : ℝ :=
      6*a^4*b^2*(1-b) +
      18*a^2*(1-a)*b*(1-b) +
      164*a*(1-a)*b*(1-b) +
      57*b*(1-b) +
      57*a*(1-a)

theorem rankinSparseBlock5_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_5
  positivity

noncomputable def rankinSparseBlock5_6 (a b : ℝ) : ℝ :=
      4*a^2*(1-a)*b^4 +
      56*a*(1-a)*b^2*(1-b) +
      19*a*b^4 +
      14*a^4*b

theorem rankinSparseBlock5_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_6
  positivity

noncomputable def rankinSparseBlock5_7 (a b : ℝ) : ℝ :=
      9*a*b^2*(1-b) +
      36*a^2*(1-a)*b

theorem rankinSparseBlock5_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_7
  positivity

noncomputable def rankinSparseBlock5_8 (a b : ℝ) : ℝ :=
      5*a^4*b^3*(1-b) +
      11*a^2*b^4 +
      7*a^4*b^2

theorem rankinSparseBlock5_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_8
  positivity

noncomputable def rankinSparseBlock5_9 (a b : ℝ) : ℝ :=
      a^4*b^4*(1-b) +
      a^4*(1-a)*b^4 +
      8*a^2*(1-a)*b^2*(1-b)

theorem rankinSparseBlock5_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_9
  positivity

noncomputable def rankinSparseBlock6_0 (a b : ℝ) : ℝ :=
      22*b

theorem rankinSparseBlock6_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_0
  positivity

noncomputable def rankinSparseBlock6_1 (a b : ℝ) : ℝ :=
      59*a

theorem rankinSparseBlock6_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_1
  positivity

noncomputable def rankinSparseBlock6_3 (a b : ℝ) : ℝ :=
      159*a*b

theorem rankinSparseBlock6_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_3
  positivity

noncomputable def rankinSparseBlock6_4 (a b : ℝ) : ℝ :=
      46*a^2*(1-a)*b^3 +
      15*a^4*b*(1-b) +
      71*(1-a)*b*(1-b) +
      6*a^2*(1-a)*(1-b) +
      71*a*(1-a)*(1-b) +
      6*b^4 +
      18*b^2*(1-b) +
      a^4 +
      18*a^2*(1-a)

theorem rankinSparseBlock6_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_4
  positivity

noncomputable def rankinSparseBlock6_5 (a b : ℝ) : ℝ :=
      12*a^4*b^2*(1-b) +
      5*a^2*(1-a)*b^3 +
      224*a*(1-a)*b*(1-b) +
      168*(1-a)*b*(1-b) +
      18*a^2*(1-a)*(1-b) +
      168*a*(1-a)*(1-b) +
      5*a^4

theorem rankinSparseBlock6_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_5
  positivity

noncomputable def rankinSparseBlock6_6 (a b : ℝ) : ℝ :=
      12*a^2*(1-a)*b^4 +
      54*a*(1-a)*b^2*(1-b) +
      49*a^2*(1-a)*b*(1-b) +
      36*a*b^4 +
      16*a^4*b

theorem rankinSparseBlock6_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_6
  positivity

noncomputable def rankinSparseBlock6_7 (a b : ℝ) : ℝ :=
      2*a^4*(1-a)*b^4*(1-b) +
      4*a^3*b^4*(1-b) +
      4*a^4*(1-a)*b^3

theorem rankinSparseBlock6_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_7
  positivity

noncomputable def rankinSparseBlock6_8 (a b : ℝ) : ℝ :=
      16*a^4*b^3*(1-b)

theorem rankinSparseBlock6_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_8
  positivity

noncomputable def rankinSparseBlock6_9 (a b : ℝ) : ℝ :=
      a^4*b^4*(1-b) +
      a^4*(1-a)*b^4

theorem rankinSparseBlock6_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_9
  positivity

noncomputable def rankinSparseBlock7_0 (a b : ℝ) : ℝ :=
      24*b

theorem rankinSparseBlock7_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_0
  positivity

noncomputable def rankinSparseBlock7_1 (a b : ℝ) : ℝ :=
      83*a

theorem rankinSparseBlock7_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_1
  positivity

noncomputable def rankinSparseBlock7_2 (a b : ℝ) : ℝ :=
      82*b*(1-b) +
      82*a*(1-a)

theorem rankinSparseBlock7_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_2
  positivity

noncomputable def rankinSparseBlock7_3 (a b : ℝ) : ℝ :=
      6*(1-a)*b^4 +
      5*(1-a)*b^2*(1-b) +
      176*a*b +
      342*b*(1-b) +
      342*a*(1-a)

theorem rankinSparseBlock7_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_3
  positivity

noncomputable def rankinSparseBlock7_4 (a b : ℝ) : ℝ :=
      34*a*(1-a)*b^4 +
      17*a^4*b*(1-b) +
      4*b^4 +
      25*b^2*(1-b)

theorem rankinSparseBlock7_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_4
  positivity

noncomputable def rankinSparseBlock7_5 (a b : ℝ) : ℝ :=
      a^4*b^2*(1-b) +
      31*a*(1-a)*b^4 +
      7*a^4*b*(1-b) +
      248*a*(1-a)*b*(1-b) +
      42*(1-a)*b*(1-b) +
      72*a^2*(1-a)*(1-b) +
      42*a*(1-a)*(1-b) +
      15*a^4

theorem rankinSparseBlock7_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_5
  positivity

noncomputable def rankinSparseBlock7_6 (a b : ℝ) : ℝ :=
      7*a^3*(1-a)*b^4*(1-b) +
      7*a^4*(1-a)*b^3*(1-b) +
      38*a^2*(1-a)*b^4 +
      11*a^4*b^2*(1-b) +
      6*a^2*b^4*(1-b) +
      14*a*(1-a)*b^2*(1-b) +
      6*a^4*(1-a)*b^2 +
      55*a^2*(1-a)*b*(1-b)

theorem rankinSparseBlock7_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_6
  positivity

noncomputable def rankinSparseBlock7_7 (a b : ℝ) : ℝ :=
      a^3*b^4*(1-b) +
      a^4*(1-a)*b^3

theorem rankinSparseBlock7_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_7
  positivity

noncomputable def rankinSparseBlock7_8 (a b : ℝ) : ℝ :=
      20*a^4*b^3*(1-b)

theorem rankinSparseBlock7_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_8
  positivity

noncomputable def rankinSparseBlock8_0 (a b : ℝ) : ℝ :=
      24*b

theorem rankinSparseBlock8_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_0
  positivity

noncomputable def rankinSparseBlock8_1 (a b : ℝ) : ℝ :=
      107*a

theorem rankinSparseBlock8_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_1
  positivity

noncomputable def rankinSparseBlock8_3 (a b : ℝ) : ℝ :=
      108*a^2*b^2*(1-b) +
      8*(1-a)*b^4 +
      28*(1-a)*b^2*(1-b) +
      18*a^4*(1-b) +
      52*a*b +
      4*a^2*(1-a)

theorem rankinSparseBlock8_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_3
  positivity

noncomputable def rankinSparseBlock8_4 (a b : ℝ) : ℝ :=
      43*a^2*(1-a)*b^3 +
      a*(1-a)*b^4*(1-b) +
      22*a^2*b^2*(1-b) +
      a^4*(1-a)*b*(1-b) +
      9*(1-a)*b^2*(1-b) +
      12*a^4*(1-b) +
      48*a*b +
      b^4 +
      134*a^2*(1-a)

theorem rankinSparseBlock8_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_4
  positivity

noncomputable def rankinSparseBlock8_5 (a b : ℝ) : ℝ :=
      8*a^4*b^4 +
      11*a^2*(1-a)*b^4*(1-b) +
      11*a^4*(1-a)*b^2*(1-b) +
      11*a*(1-a)*b^4 +
      162*a*(1-a)*b*(1-b) +
      3*a*b^4*(1-b) +
      3*a^4*(1-a)*b +
      23*a^4*b

theorem rankinSparseBlock8_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_5
  positivity

noncomputable def rankinSparseBlock8_6 (a b : ℝ) : ℝ :=
      a^3*(1-a)*b^4*(1-b) +
      a^4*(1-a)*b^3*(1-b) +
      2*a^2*(1-a)*b^4*(1-b) +
      48*a^2*(1-a)*b^4 +
      2*a^4*(1-a)*b^2*(1-b) +
      4*a^4*b^2*(1-b)

theorem rankinSparseBlock8_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_6
  positivity

noncomputable def rankinSparseBlock8_7 (a b : ℝ) : ℝ :=
      a^3*(1-a)*b^4*(1-b) +
      a^4*(1-a)*b^3*(1-b)

theorem rankinSparseBlock8_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_7
  positivity

noncomputable def rankinSparseBlock9_0 (a b : ℝ) : ℝ :=
      21*b

theorem rankinSparseBlock9_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_0
  positivity

noncomputable def rankinSparseBlock9_1 (a b : ℝ) : ℝ :=
      112*b*(1-b) +
      110*a*(1-a) +
      83*a

theorem rankinSparseBlock9_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_1
  positivity

noncomputable def rankinSparseBlock9_2 (a b : ℝ) : ℝ :=
      92*a*(1-a)*b^2 +
      264*a*b*(1-b) +
      12*a^2*(1-a)*(1-b) +
      12*b^2*(1-b) +
      2*a*(1-a) +
      45*a

theorem rankinSparseBlock9_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_2
  positivity

noncomputable def rankinSparseBlock9_3 (a b : ℝ) : ℝ :=
      138*a^2*(1-a)*b^2 +
      24*a*(1-a)*b^2 +
      (1-a)*b^4*(1-b) +
      4*(1-a)*b^4 +
      61*a*b*(1-b) +
      a^4*(1-a)*(1-b) +
      62*a^2*(1-a)*(1-b) +
      209*a*(1-a)*b +
      9*b^2*(1-b)

theorem rankinSparseBlock9_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_3
  positivity

noncomputable def rankinSparseBlock9_4 (a b : ℝ) : ℝ :=
      11*a^2*(1-a)*b^3 +
      8*a*(1-a)*b^4*(1-b) +
      80*a^2*b^2*(1-b) +
      8*a^4*(1-a)*b*(1-b) +
      28*a^4*b*(1-b) +
      14*a*b^4 +
      2*a^4*(1-b) +
      2*b^4

theorem rankinSparseBlock9_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_4
  positivity

noncomputable def rankinSparseBlock9_5 (a b : ℝ) : ℝ :=
      24*a^4*b^4 +
      80*a^2*(1-a)*b^3 +
      3*a^2*b^4*(1-b) +
      18*a^2*b^4 +
      3*a^4*(1-a)*b^2

theorem rankinSparseBlock9_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_5
  positivity

noncomputable def rankinSparseBlock9_6 (a b : ℝ) : ℝ :=
      20*a^4*b^4

theorem rankinSparseBlock9_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_6
  positivity

noncomputable def rankinSparseBlock10_0 (a b : ℝ) : ℝ :=
      106*a*(1-b) +
      18*b

theorem rankinSparseBlock10_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_0
  positivity

noncomputable def rankinSparseBlock10_1 (a b : ℝ) : ℝ :=
      85*a*(1-b) +
      22*b*(1-b)

theorem rankinSparseBlock10_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_1
  positivity

noncomputable def rankinSparseBlock10_2 (a b : ℝ) : ℝ :=
      16*a*b^2*(1-b) +
      28*a*(1-a)*(1-b) +
      4*b*(1-b)

theorem rankinSparseBlock10_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_2
  positivity

noncomputable def rankinSparseBlock10_3 (a b : ℝ) : ℝ :=
      4*(1-a)^2*b^4 +
      4*a^4*(1-b)^2 +
      22*a^4*b^2 +
      8*a^2*(1-a)*b^2 +
      200*a*(1-a)*b^2 +
      (1-a)*b^4*(1-b) +
      38*a*b^2*(1-b) +
      a^4*(1-a)*(1-b) +
      107*a^2*(1-a)*b

theorem rankinSparseBlock10_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_3
  positivity

noncomputable def rankinSparseBlock10_4 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b^4*(1-b) +
      48*a^3*b^4 +
      a^4*(1-a)*b^2*(1-b) +
      68*a^4*b^3 +
      4*a^4*b^2 +
      42*a^2*(1-a)*b^2

theorem rankinSparseBlock10_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_4
  positivity

noncomputable def rankinSparseBlock11_0 (a b : ℝ) : ℝ :=
      7*b +
      31*a

theorem rankinSparseBlock11_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_0
  positivity

noncomputable def rankinSparseBlock11_1 (a b : ℝ) : ℝ :=
      2*a^4*b*(1-b) +
      88*a*b*(1-b) +
      116*a*(1-a)*b +
      16*a*(1-b) +
      24*a*(1-a)

theorem rankinSparseBlock11_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_1
  positivity

noncomputable def rankinSparseBlock11_2 (a b : ℝ) : ℝ :=
      2*a^2*b^4 +
      64*a*(1-a)*b^2*(1-b) +
      10*a^4*b*(1-b) +
      92*a^2*(1-a)*b*(1-b) +
      12*a*b^4 +
      6*(1-a)*b^2*(1-b) +
      6*a^2*(1-a)*(1-b) +
      172*a*(1-a)*b

theorem rankinSparseBlock11_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_2
  positivity

noncomputable def rankinSparseBlock11_3 (a b : ℝ) : ℝ :=
      20*a^4*b^2*(1-b) +
      72*a^2*(1-a)*b^2*(1-b) +
      28*a^2*b^4 +
      10*a^2*b^2*(1-b)

theorem rankinSparseBlock11_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_3
  positivity

noncomputable def rankinSparseBlock11_4 (a b : ℝ) : ℝ :=
      a^3*b^4*(1-b) +
      a^4*(1-a)*b^3

theorem rankinSparseBlock11_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_4
  positivity

noncomputable def rankinSparseBlock12_0 (a b : ℝ) : ℝ :=
      20*(1-a)*b*(1-b) +
      48*a*(1-a)*(1-b) +
      28*b*(1-b) +
      4*b +
      20*a

theorem rankinSparseBlock12_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock12_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock12_0
  positivity

noncomputable def rankinSparseBlock12_1 (a b : ℝ) : ℝ :=
      2*a*(1-a)*b^4 +
      8*(1-a)^2*b^2*(1-b) +
      2*a^2*(1-a)*(1-b)^2 +
      42*a*(1-a)*b*(1-b) +
      2*(1-a)*b^4 +
      2*a^4*(1-b) +
      51*a*b

theorem rankinSparseBlock12_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock12_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock12_1
  positivity

noncomputable def rankinSparseBlock12_2 (a b : ℝ) : ℝ :=
      2*a^4*b^3 +
      2*(1-a)^2*b^2*(1-b) +
      14*a^4*b^2 +
      8*a^2*(1-a)*(1-b)^2 +
      28*a^2*(1-a)*b^2 +
      2*(1-a)*b^2*(1-b) +
      2*a^2*(1-a)*(1-b)

theorem rankinSparseBlock12_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock12_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock12_2
  positivity

noncomputable def rankinSparseBlock12_3 (a b : ℝ) : ℝ :=
      18*a^4*b^3

theorem rankinSparseBlock12_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock12_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock12_3
  positivity

noncomputable def rankinSparseBlock13_0 (a b : ℝ) : ℝ :=
      2*a*(1-a)*b^3 +
      4*a^3*b^2 +
      31*a*(1-a)*b^2 +
      4*a*b^3 +
      39*a*b*(1-b) +
      31*a*(1-a)*b +
      6*(1-a)*b +
      6*a*(1-b) +
      2*b*(1-b) +
      2*a*(1-a)

theorem rankinSparseBlock13_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock13_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock13_0
  positivity

noncomputable def rankinSparseBlock13_1 (a b : ℝ) : ℝ :=
      2*a^4*b^2*(1-b) +
      6*a^2*(1-a)*(1-b)^3 +
      6*a^3*b^2*(1-b) +
      2*a^2*b^4 +
      16*a^2*b^3 +
      10*a^3*b^2 +
      2*(1-a)^2*b^2 +
      a^2*(1-b)^2 +
      a^2*(1-b)

theorem rankinSparseBlock13_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock13_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock13_1
  positivity

noncomputable def rankinSparseBlock14_0 (a b : ℝ) : ℝ :=
      2*(1-a)^2*b^3 +
      4*a^3*b*(1-b) +
      5*a*(1-a)*b*(1-b) +
      26*a^2*b^2 +
      2*(1-a)*b^3 +
      2*(1-a)*b*(1-b) +
      5*a*b^2 +
      4*a^3*(1-b) +
      2*a*(1-a)*(1-b)

theorem rankinSparseBlock14_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock14_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock14_0
  positivity

noncomputable def rankinSparseBlock14_1 (a b : ℝ) : ℝ :=
      2*a^4*b^3

theorem rankinSparseBlock14_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock14_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock14_1
  positivity

noncomputable def rankinSparseBlock15_0 (a b : ℝ) : ℝ :=
      a*b +
      b +
      a

theorem rankinSparseBlock15_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock15_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock15_0
  positivity

noncomputable def rankinSparseBlock16_0 (a b : ℝ) : ℝ :=
      a*b

theorem rankinSparseBlock16_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock16_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock16_0
  positivity

noncomputable def rankinSparseBlock17_0 (a b : ℝ) : ℝ :=
      a*b

theorem rankinSparseBlock17_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock17_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock17_0
  positivity

noncomputable def rankinCoupledSparseBlockCertificate (r a b : ℝ) : ℝ :=
      (1-r)^6*rankinSparseBlock0_6 a b +
      (1-r)^7*rankinSparseBlock0_7 a b +
      r*rankinSparseBlock1_0 a b +
      r*(1-r)*rankinSparseBlock1_1 a b +
      r*(1-r)^3*rankinSparseBlock1_3 a b +
      r*(1-r)^4*rankinSparseBlock1_4 a b +
      r*(1-r)^5*rankinSparseBlock1_5 a b +
      r*(1-r)^6*rankinSparseBlock1_6 a b +
      r*(1-r)^7*rankinSparseBlock1_7 a b +
      r^2*rankinSparseBlock2_0 a b +
      r^2*(1-r)*rankinSparseBlock2_1 a b +
      r^2*(1-r)^3*rankinSparseBlock2_3 a b +
      r^2*(1-r)^4*rankinSparseBlock2_4 a b +
      r^2*(1-r)^5*rankinSparseBlock2_5 a b +
      r^2*(1-r)^6*rankinSparseBlock2_6 a b +
      r^2*(1-r)^7*rankinSparseBlock2_7 a b +
      r^2*(1-r)^8*rankinSparseBlock2_8 a b +
      r^2*(1-r)^9*rankinSparseBlock2_9 a b +
      r^3*rankinSparseBlock3_0 a b +
      r^3*(1-r)*rankinSparseBlock3_1 a b +
      r^3*(1-r)^3*rankinSparseBlock3_3 a b +
      r^3*(1-r)^4*rankinSparseBlock3_4 a b +
      r^3*(1-r)^5*rankinSparseBlock3_5 a b +
      r^3*(1-r)^6*rankinSparseBlock3_6 a b +
      r^3*(1-r)^7*rankinSparseBlock3_7 a b +
      r^3*(1-r)^8*rankinSparseBlock3_8 a b +
      r^3*(1-r)^9*rankinSparseBlock3_9 a b +
      r^4*rankinSparseBlock4_0 a b +
      r^4*(1-r)*rankinSparseBlock4_1 a b +
      r^4*(1-r)^3*rankinSparseBlock4_3 a b +
      r^4*(1-r)^4*rankinSparseBlock4_4 a b +
      r^4*(1-r)^5*rankinSparseBlock4_5 a b +
      r^4*(1-r)^6*rankinSparseBlock4_6 a b +
      r^4*(1-r)^7*rankinSparseBlock4_7 a b +
      r^4*(1-r)^8*rankinSparseBlock4_8 a b +
      r^4*(1-r)^9*rankinSparseBlock4_9 a b +
      r^5*rankinSparseBlock5_0 a b +
      r^5*(1-r)*rankinSparseBlock5_1 a b +
      r^5*(1-r)^3*rankinSparseBlock5_3 a b +
      r^5*(1-r)^4*rankinSparseBlock5_4 a b +
      r^5*(1-r)^5*rankinSparseBlock5_5 a b +
      r^5*(1-r)^6*rankinSparseBlock5_6 a b +
      r^5*(1-r)^7*rankinSparseBlock5_7 a b +
      r^5*(1-r)^8*rankinSparseBlock5_8 a b +
      r^5*(1-r)^9*rankinSparseBlock5_9 a b +
      r^6*rankinSparseBlock6_0 a b +
      r^6*(1-r)*rankinSparseBlock6_1 a b +
      r^6*(1-r)^3*rankinSparseBlock6_3 a b +
      r^6*(1-r)^4*rankinSparseBlock6_4 a b +
      r^6*(1-r)^5*rankinSparseBlock6_5 a b +
      r^6*(1-r)^6*rankinSparseBlock6_6 a b +
      r^6*(1-r)^7*rankinSparseBlock6_7 a b +
      r^6*(1-r)^8*rankinSparseBlock6_8 a b +
      r^6*(1-r)^9*rankinSparseBlock6_9 a b +
      r^7*rankinSparseBlock7_0 a b +
      r^7*(1-r)*rankinSparseBlock7_1 a b +
      r^7*(1-r)^2*rankinSparseBlock7_2 a b +
      r^7*(1-r)^3*rankinSparseBlock7_3 a b +
      r^7*(1-r)^4*rankinSparseBlock7_4 a b +
      r^7*(1-r)^5*rankinSparseBlock7_5 a b +
      r^7*(1-r)^6*rankinSparseBlock7_6 a b +
      r^7*(1-r)^7*rankinSparseBlock7_7 a b +
      r^7*(1-r)^8*rankinSparseBlock7_8 a b +
      r^8*rankinSparseBlock8_0 a b +
      r^8*(1-r)*rankinSparseBlock8_1 a b +
      r^8*(1-r)^3*rankinSparseBlock8_3 a b +
      r^8*(1-r)^4*rankinSparseBlock8_4 a b +
      r^8*(1-r)^5*rankinSparseBlock8_5 a b +
      r^8*(1-r)^6*rankinSparseBlock8_6 a b +
      r^8*(1-r)^7*rankinSparseBlock8_7 a b +
      r^9*rankinSparseBlock9_0 a b +
      r^9*(1-r)*rankinSparseBlock9_1 a b +
      r^9*(1-r)^2*rankinSparseBlock9_2 a b +
      r^9*(1-r)^3*rankinSparseBlock9_3 a b +
      r^9*(1-r)^4*rankinSparseBlock9_4 a b +
      r^9*(1-r)^5*rankinSparseBlock9_5 a b +
      r^9*(1-r)^6*rankinSparseBlock9_6 a b +
      r^10*rankinSparseBlock10_0 a b +
      r^10*(1-r)*rankinSparseBlock10_1 a b +
      r^10*(1-r)^2*rankinSparseBlock10_2 a b +
      r^10*(1-r)^3*rankinSparseBlock10_3 a b +
      r^10*(1-r)^4*rankinSparseBlock10_4 a b +
      r^11*rankinSparseBlock11_0 a b +
      r^11*(1-r)*rankinSparseBlock11_1 a b +
      r^11*(1-r)^2*rankinSparseBlock11_2 a b +
      r^11*(1-r)^3*rankinSparseBlock11_3 a b +
      r^11*(1-r)^4*rankinSparseBlock11_4 a b +
      r^12*rankinSparseBlock12_0 a b +
      r^12*(1-r)*rankinSparseBlock12_1 a b +
      r^12*(1-r)^2*rankinSparseBlock12_2 a b +
      r^12*(1-r)^3*rankinSparseBlock12_3 a b +
      r^13*rankinSparseBlock13_0 a b +
      r^13*(1-r)*rankinSparseBlock13_1 a b +
      r^14*rankinSparseBlock14_0 a b +
      r^14*(1-r)*rankinSparseBlock14_1 a b +
      r^15*rankinSparseBlock15_0 a b +
      r^16*rankinSparseBlock16_0 a b +
      r^17*rankinSparseBlock17_0 a b

theorem rankinCoupledSparseBlockCertificate_nonneg (r a b : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinCoupledSparseBlockCertificate r a b := by
  have hr2 : 0 ≤ 1-r := by linarith
  have h0_6 := rankinSparseBlock0_6_nonneg a b ha ha1 hb hb1
  have h0_7 := rankinSparseBlock0_7_nonneg a b ha ha1 hb hb1
  have h1_0 := rankinSparseBlock1_0_nonneg a b ha ha1 hb hb1
  have h1_1 := rankinSparseBlock1_1_nonneg a b ha ha1 hb hb1
  have h1_3 := rankinSparseBlock1_3_nonneg a b ha ha1 hb hb1
  have h1_4 := rankinSparseBlock1_4_nonneg a b ha ha1 hb hb1
  have h1_5 := rankinSparseBlock1_5_nonneg a b ha ha1 hb hb1
  have h1_6 := rankinSparseBlock1_6_nonneg a b ha ha1 hb hb1
  have h1_7 := rankinSparseBlock1_7_nonneg a b ha ha1 hb hb1
  have h2_0 := rankinSparseBlock2_0_nonneg a b ha ha1 hb hb1
  have h2_1 := rankinSparseBlock2_1_nonneg a b ha ha1 hb hb1
  have h2_3 := rankinSparseBlock2_3_nonneg a b ha ha1 hb hb1
  have h2_4 := rankinSparseBlock2_4_nonneg a b ha ha1 hb hb1
  have h2_5 := rankinSparseBlock2_5_nonneg a b ha ha1 hb hb1
  have h2_6 := rankinSparseBlock2_6_nonneg a b ha ha1 hb hb1
  have h2_7 := rankinSparseBlock2_7_nonneg a b ha ha1 hb hb1
  have h2_8 := rankinSparseBlock2_8_nonneg a b ha ha1 hb hb1
  have h2_9 := rankinSparseBlock2_9_nonneg a b ha ha1 hb hb1
  have h3_0 := rankinSparseBlock3_0_nonneg a b ha ha1 hb hb1
  have h3_1 := rankinSparseBlock3_1_nonneg a b ha ha1 hb hb1
  have h3_3 := rankinSparseBlock3_3_nonneg a b ha ha1 hb hb1
  have h3_4 := rankinSparseBlock3_4_nonneg a b ha ha1 hb hb1
  have h3_5 := rankinSparseBlock3_5_nonneg a b ha ha1 hb hb1
  have h3_6 := rankinSparseBlock3_6_nonneg a b ha ha1 hb hb1
  have h3_7 := rankinSparseBlock3_7_nonneg a b ha ha1 hb hb1
  have h3_8 := rankinSparseBlock3_8_nonneg a b ha ha1 hb hb1
  have h3_9 := rankinSparseBlock3_9_nonneg a b ha ha1 hb hb1
  have h4_0 := rankinSparseBlock4_0_nonneg a b ha ha1 hb hb1
  have h4_1 := rankinSparseBlock4_1_nonneg a b ha ha1 hb hb1
  have h4_3 := rankinSparseBlock4_3_nonneg a b ha ha1 hb hb1
  have h4_4 := rankinSparseBlock4_4_nonneg a b ha ha1 hb hb1
  have h4_5 := rankinSparseBlock4_5_nonneg a b ha ha1 hb hb1
  have h4_6 := rankinSparseBlock4_6_nonneg a b ha ha1 hb hb1
  have h4_7 := rankinSparseBlock4_7_nonneg a b ha ha1 hb hb1
  have h4_8 := rankinSparseBlock4_8_nonneg a b ha ha1 hb hb1
  have h4_9 := rankinSparseBlock4_9_nonneg a b ha ha1 hb hb1
  have h5_0 := rankinSparseBlock5_0_nonneg a b ha ha1 hb hb1
  have h5_1 := rankinSparseBlock5_1_nonneg a b ha ha1 hb hb1
  have h5_3 := rankinSparseBlock5_3_nonneg a b ha ha1 hb hb1
  have h5_4 := rankinSparseBlock5_4_nonneg a b ha ha1 hb hb1
  have h5_5 := rankinSparseBlock5_5_nonneg a b ha ha1 hb hb1
  have h5_6 := rankinSparseBlock5_6_nonneg a b ha ha1 hb hb1
  have h5_7 := rankinSparseBlock5_7_nonneg a b ha ha1 hb hb1
  have h5_8 := rankinSparseBlock5_8_nonneg a b ha ha1 hb hb1
  have h5_9 := rankinSparseBlock5_9_nonneg a b ha ha1 hb hb1
  have h6_0 := rankinSparseBlock6_0_nonneg a b ha ha1 hb hb1
  have h6_1 := rankinSparseBlock6_1_nonneg a b ha ha1 hb hb1
  have h6_3 := rankinSparseBlock6_3_nonneg a b ha ha1 hb hb1
  have h6_4 := rankinSparseBlock6_4_nonneg a b ha ha1 hb hb1
  have h6_5 := rankinSparseBlock6_5_nonneg a b ha ha1 hb hb1
  have h6_6 := rankinSparseBlock6_6_nonneg a b ha ha1 hb hb1
  have h6_7 := rankinSparseBlock6_7_nonneg a b ha ha1 hb hb1
  have h6_8 := rankinSparseBlock6_8_nonneg a b ha ha1 hb hb1
  have h6_9 := rankinSparseBlock6_9_nonneg a b ha ha1 hb hb1
  have h7_0 := rankinSparseBlock7_0_nonneg a b ha ha1 hb hb1
  have h7_1 := rankinSparseBlock7_1_nonneg a b ha ha1 hb hb1
  have h7_2 := rankinSparseBlock7_2_nonneg a b ha ha1 hb hb1
  have h7_3 := rankinSparseBlock7_3_nonneg a b ha ha1 hb hb1
  have h7_4 := rankinSparseBlock7_4_nonneg a b ha ha1 hb hb1
  have h7_5 := rankinSparseBlock7_5_nonneg a b ha ha1 hb hb1
  have h7_6 := rankinSparseBlock7_6_nonneg a b ha ha1 hb hb1
  have h7_7 := rankinSparseBlock7_7_nonneg a b ha ha1 hb hb1
  have h7_8 := rankinSparseBlock7_8_nonneg a b ha ha1 hb hb1
  have h8_0 := rankinSparseBlock8_0_nonneg a b ha ha1 hb hb1
  have h8_1 := rankinSparseBlock8_1_nonneg a b ha ha1 hb hb1
  have h8_3 := rankinSparseBlock8_3_nonneg a b ha ha1 hb hb1
  have h8_4 := rankinSparseBlock8_4_nonneg a b ha ha1 hb hb1
  have h8_5 := rankinSparseBlock8_5_nonneg a b ha ha1 hb hb1
  have h8_6 := rankinSparseBlock8_6_nonneg a b ha ha1 hb hb1
  have h8_7 := rankinSparseBlock8_7_nonneg a b ha ha1 hb hb1
  have h9_0 := rankinSparseBlock9_0_nonneg a b ha ha1 hb hb1
  have h9_1 := rankinSparseBlock9_1_nonneg a b ha ha1 hb hb1
  have h9_2 := rankinSparseBlock9_2_nonneg a b ha ha1 hb hb1
  have h9_3 := rankinSparseBlock9_3_nonneg a b ha ha1 hb hb1
  have h9_4 := rankinSparseBlock9_4_nonneg a b ha ha1 hb hb1
  have h9_5 := rankinSparseBlock9_5_nonneg a b ha ha1 hb hb1
  have h9_6 := rankinSparseBlock9_6_nonneg a b ha ha1 hb hb1
  have h10_0 := rankinSparseBlock10_0_nonneg a b ha ha1 hb hb1
  have h10_1 := rankinSparseBlock10_1_nonneg a b ha ha1 hb hb1
  have h10_2 := rankinSparseBlock10_2_nonneg a b ha ha1 hb hb1
  have h10_3 := rankinSparseBlock10_3_nonneg a b ha ha1 hb hb1
  have h10_4 := rankinSparseBlock10_4_nonneg a b ha ha1 hb hb1
  have h11_0 := rankinSparseBlock11_0_nonneg a b ha ha1 hb hb1
  have h11_1 := rankinSparseBlock11_1_nonneg a b ha ha1 hb hb1
  have h11_2 := rankinSparseBlock11_2_nonneg a b ha ha1 hb hb1
  have h11_3 := rankinSparseBlock11_3_nonneg a b ha ha1 hb hb1
  have h11_4 := rankinSparseBlock11_4_nonneg a b ha ha1 hb hb1
  have h12_0 := rankinSparseBlock12_0_nonneg a b ha ha1 hb hb1
  have h12_1 := rankinSparseBlock12_1_nonneg a b ha ha1 hb hb1
  have h12_2 := rankinSparseBlock12_2_nonneg a b ha ha1 hb hb1
  have h12_3 := rankinSparseBlock12_3_nonneg a b ha ha1 hb hb1
  have h13_0 := rankinSparseBlock13_0_nonneg a b ha ha1 hb hb1
  have h13_1 := rankinSparseBlock13_1_nonneg a b ha ha1 hb hb1
  have h14_0 := rankinSparseBlock14_0_nonneg a b ha ha1 hb hb1
  have h14_1 := rankinSparseBlock14_1_nonneg a b ha ha1 hb hb1
  have h15_0 := rankinSparseBlock15_0_nonneg a b ha ha1 hb hb1
  have h16_0 := rankinSparseBlock16_0_nonneg a b ha ha1 hb hb1
  have h17_0 := rankinSparseBlock17_0_nonneg a b ha ha1 hb hb1
  unfold rankinCoupledSparseBlockCertificate
  positivity

theorem rankin_coupled_sparse_block_polynomial_certificate (r a b : ℝ) :
    let x := r^2
    let y := x+a*(r-x)
    let z := x+b*(r-x)
    (1-x^3)^2*(1-x^4)*((1-y+x)*(1-z+x))
      - (1-y*z)*(1-y*z^2)*(1-y^2*z)*((1-y+x)*(1-z+x)+y*z)
      = r^4*(1-r)^3*rankinCoupledSparseBlockCertificate r a b := by
  dsimp only
  unfold rankinCoupledSparseBlockCertificate rankinSparseBlock0_6 rankinSparseBlock0_7 rankinSparseBlock1_0 rankinSparseBlock1_1 rankinSparseBlock1_3 rankinSparseBlock1_4 rankinSparseBlock1_5 rankinSparseBlock1_6 rankinSparseBlock1_7 rankinSparseBlock2_0 rankinSparseBlock2_1 rankinSparseBlock2_3 rankinSparseBlock2_4 rankinSparseBlock2_5 rankinSparseBlock2_6 rankinSparseBlock2_7 rankinSparseBlock2_8 rankinSparseBlock2_9 rankinSparseBlock3_0 rankinSparseBlock3_1 rankinSparseBlock3_3 rankinSparseBlock3_4 rankinSparseBlock3_5 rankinSparseBlock3_6 rankinSparseBlock3_7 rankinSparseBlock3_8 rankinSparseBlock3_9 rankinSparseBlock4_0 rankinSparseBlock4_1 rankinSparseBlock4_3 rankinSparseBlock4_4 rankinSparseBlock4_5 rankinSparseBlock4_6 rankinSparseBlock4_7 rankinSparseBlock4_8 rankinSparseBlock4_9 rankinSparseBlock5_0 rankinSparseBlock5_1 rankinSparseBlock5_3 rankinSparseBlock5_4 rankinSparseBlock5_5 rankinSparseBlock5_6 rankinSparseBlock5_7 rankinSparseBlock5_8 rankinSparseBlock5_9 rankinSparseBlock6_0 rankinSparseBlock6_1 rankinSparseBlock6_3 rankinSparseBlock6_4 rankinSparseBlock6_5 rankinSparseBlock6_6 rankinSparseBlock6_7 rankinSparseBlock6_8 rankinSparseBlock6_9 rankinSparseBlock7_0 rankinSparseBlock7_1 rankinSparseBlock7_2 rankinSparseBlock7_3 rankinSparseBlock7_4 rankinSparseBlock7_5 rankinSparseBlock7_6 rankinSparseBlock7_7 rankinSparseBlock7_8 rankinSparseBlock8_0 rankinSparseBlock8_1 rankinSparseBlock8_3 rankinSparseBlock8_4 rankinSparseBlock8_5 rankinSparseBlock8_6 rankinSparseBlock8_7 rankinSparseBlock9_0 rankinSparseBlock9_1 rankinSparseBlock9_2 rankinSparseBlock9_3 rankinSparseBlock9_4 rankinSparseBlock9_5 rankinSparseBlock9_6 rankinSparseBlock10_0 rankinSparseBlock10_1 rankinSparseBlock10_2 rankinSparseBlock10_3 rankinSparseBlock10_4 rankinSparseBlock11_0 rankinSparseBlock11_1 rankinSparseBlock11_2 rankinSparseBlock11_3 rankinSparseBlock11_4 rankinSparseBlock12_0 rankinSparseBlock12_1 rankinSparseBlock12_2 rankinSparseBlock12_3 rankinSparseBlock13_0 rankinSparseBlock13_1 rankinSparseBlock14_0 rankinSparseBlock14_1 rankinSparseBlock15_0 rankinSparseBlock16_0 rankinSparseBlock17_0
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Helfgott

theorem rankin_coupled_euler_factor_upper_sparse_block (x y z : ℝ) (hx : 0 < x)
    (hxy : x ≤ y) (hxz : x ≤ z) (hy : y < 1) (hz : z < 1)
    (hysq : y^2 ≤ x) (hzsq : z^2 ≤ x) :
    1+y*z/((1-y+x)*(1-z+x)) ≤
      (1-x^3)^2*(1-x^4)/((1-y*z)*(1-y*z^2)*(1-y^2*z)) := by
  have hy0 : 0 ≤ y := hx.le.trans hxy
  have hz0 : 0 ≤ z := hx.le.trans hxz
  have hx1 : x < 1 := hxy.trans_lt hy
  let r := Real.sqrt x
  have hr0 : 0 < r := Real.sqrt_pos.2 hx
  have hr2 : r^2 = x := Real.sq_sqrt hx.le
  have hr1 : r < 1 := by nlinarith
  have hxr : x < r := by nlinarith
  have hyr : y ≤ r := by nlinarith
  have hzr : z ≤ r := by nlinarith
  let a := (y-x)/(r-x)
  let b := (z-x)/(r-x)
  have hden : 0 < r-x := by linarith
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hden.le
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hden.le
  have ha1 : a ≤ 1 := (div_le_one hden).2 (by linarith)
  have hb1 : b ≤ 1 := (div_le_one hden).2 (by linarith)
  have hya : x+a*(r-x)=y := by dsimp [a]; field_simp; ring
  have hzb : x+b*(r-x)=z := by dsimp [b]; field_simp; ring
  have hcert := rankin_coupled_sparse_block_polynomial_certificate r a b
  dsimp only at hcert
  rw [hr2,hya,hzb] at hcert
  have hnonneg := rankinCoupledSparseBlockCertificate_nonneg r a b hr0.le hr1.le ha0 ha1 hb0 hb1
  have hP : 0 ≤ (1-x^3)^2*(1-x^4)*((1-y+x)*(1-z+x))
      -(1-y*z)*(1-y*z^2)*(1-y^2*z)*((1-y+x)*(1-z+x)+y*z) := by
    rw [hcert]
    exact mul_nonneg (mul_nonneg (pow_nonneg hr0.le 4) (pow_nonneg (by linarith) 3)) hnonneg
  have hy2 : y^2 < 1 := by nlinarith
  have hz2 : z^2 < 1 := by nlinarith
  have hyz : y*z < 1 := (show y*z ≤ z by nlinarith).trans_lt hz
  have hyzz : y*z^2 < 1 := (show y*z^2 ≤ z^2 by nlinarith [sq_nonneg z]).trans_lt hz2
  have hyyz : y^2*z < 1 := (show y^2*z ≤ y^2 by nlinarith [sq_nonneg y]).trans_lt hy2
  have hA : 0 < (1-y+x)*(1-z+x) := mul_pos (by linarith) (by linarith)
  have hD : 0 < (1-y*z)*(1-y*z^2)*(1-y^2*z) := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have he : 1+y*z/((1-y+x)*(1-z+x)) = ((1-y+x)*(1-z+x)+y*z)/((1-y+x)*(1-z+x)) := by
    rw [add_div,div_self (ne_of_gt hA)]
  rw [he]
  apply (div_le_div_iff₀ hA hD).mpr
  nlinarith only [hP]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Helfgott

theorem rankin_coupled_prime_factor_upper_sparse_block (p s t : ℝ) (hp : 1 < p)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) :
    1+p^(-s-t)/((1-p^(-s)+p^(-1:ℝ))*(1-p^(-t)+p^(-1:ℝ))) ≤
      (1-p^(-3:ℝ))^2*(1-p^(-4:ℝ))/
        ((1-p^(-s-t))*(1-p^(-s-2*t))*(1-p^(-2*s-t))) := by
  have hp0 : 0 < p := by linarith
  have hx : 0 < p^(-1:ℝ) := Real.rpow_pos_of_pos hp0 _
  have hxy : p^(-1:ℝ) ≤ p^(-s) := Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
  have hxz : p^(-1:ℝ) ≤ p^(-t) := Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
  have hy : p^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hz : p^(-t) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hysq : (p^(-s))^2 ≤ p^(-1:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2]
    exact Real.rpow_le_rpow_of_exponent_le hp.le (by norm_num;linarith)
  have hzsq : (p^(-t))^2 ≤ p^(-1:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-t) 2]
    exact Real.rpow_le_rpow_of_exponent_le hp.le (by norm_num;linarith)
  have h := rankin_coupled_euler_factor_upper_sparse_block (p^(-1:ℝ)) (p^(-s)) (p^(-t)) hx hxy hxz hy hz hysq hzsq
  have hst : p^(-s)*p^(-t)=p^(-s-t) := by
    rw [←Real.rpow_add hp0]
    congr 1 <;> ring
  have hstt : p^(-s)*(p^(-t))^2=p^(-s-2*t) := by
    rw [←Real.rpow_mul_natCast hp0.le (-t) 2,←Real.rpow_add hp0]
    congr 1 <;> ring
  have hsst : (p^(-s))^2*p^(-t)=p^(-2*s-t) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2,←Real.rpow_add hp0]
    congr 1 <;> ring
  have h3 : (p^(-1:ℝ))^3=p^(-3:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-1) 3];norm_num
  have h4 : (p^(-1:ℝ))^4=p^(-4:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-1) 4];norm_num
  simpa only [hst,hstt,hsst,h3,h4] using h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3500000
open Finset Nat Real Filter
open scoped BigOperators Topology Classical
namespace Helfgott

lemma rankin_coupled_comparison_hasProd_sparse (s t : ℝ) (hs0 : 1/2 ≤ s) (ht0 : 1/2 ≤ t)
    (hst : 1 < s+t) :
    HasProd (fun p : Nat.Primes =>
      (1-(p : ℝ)^(-3:ℝ))^2*(1-(p : ℝ)^(-4:ℝ))/
      ((1-(p : ℝ)^(-s-t))*(1-(p : ℝ)^(-s-2*t))*(1-(p : ℝ)^(-2*s-t))))
      ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t))/
        ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ)))) := by
  have h3 := (real_zeta_euler_hasProd 3 (by norm_num)).inv₀ (ne_of_gt (real_zeta_sum_pos 3 (by norm_num)))
  have h4 := (real_zeta_euler_hasProd 4 (by norm_num)).inv₀ (ne_of_gt (real_zeta_sum_pos 4 (by norm_num)))
  have hst1 := real_zeta_euler_hasProd (s+t) hst
  have hst2 := real_zeta_euler_hasProd (s+2*t) (by linarith)
  have hst3 := real_zeta_euler_hasProd (2*s+t) (by linarith)
  have h := ((h3.pow 2).mul h4).mul ((hst1.mul hst2).mul hst3)
  have he1 : (fun n : ℕ => (n : ℝ)^(-(s+t)))=(fun n : ℕ => (n : ℝ)^(-s-t)) := by funext n;congr 1;ring
  have he2 : (fun n : ℕ => (n : ℝ)^(-(s+2*t)))=(fun n : ℕ => (n : ℝ)^(-s-2*t)) := by funext n;congr 1;ring
  have he3 : (fun n : ℕ => (n : ℝ)^(-(2*s+t)))=(fun n : ℕ => (n : ℝ)^(-2*s-t)) := by funext n;congr 1;ring
  rw [he1,he2,he3] at h
  have hv : ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))⁻¹)^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))⁻¹ *
      (((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t)))*(∑' n : ℕ,(n : ℝ)^(-2*s-t))) =
      ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
      ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := by
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow];ring
  rw [hv] at h
  apply h.congr_fun
  intro p
  have e1 : -(s+t)=-s-t := by ring
  have e2 : -(s+2*t)=-s-2*t := by ring
  have e3 : -(2*s+t)=-2*s-t := by ring
  simp only [inv_inv,e1,e2,e3,div_eq_mul_inv,mul_inv_rev]
  ring

theorem rankin_coupled_finite_prime_product_upper_sparse (P : Finset Nat.Primes) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    (∏ p∈P,(1+(p : ℝ)^(-s-t)/((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
        ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := by
  let f : Nat.Primes → ℝ := fun p => 1+(p : ℝ)^(-s-t)/
    ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))
  let g : Nat.Primes → ℝ := fun p => (1-(p : ℝ)^(-3:ℝ))^2*(1-(p : ℝ)^(-4:ℝ))/
    ((1-(p : ℝ)^(-s-t))*(1-(p : ℝ)^(-s-2*t))*(1-(p : ℝ)^(-2*s-t)))
  have hf1 (p : Nat.Primes) : 1 ≤ f p := by
    have hp : (1:ℝ)<p := by exact_mod_cast p.property.one_lt
    have hp0 : (0:ℝ)<p := by linarith
    have hy : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    have hz : (p : ℝ)^(-t)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    dsimp [f]
    have hd : 0<(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)) :=
      mul_pos (by linarith [Real.rpow_pos_of_pos hp0 (-1)]) (by linarith [Real.rpow_pos_of_pos hp0 (-1)])
    exact le_add_of_nonneg_right (div_nonneg (Real.rpow_nonneg hp0.le _) hd.le)
  have hfg (p : Nat.Primes) : f p ≤ g p :=
    rankin_coupled_prime_factor_upper_sparse_block (p : ℝ) s t (by exact_mod_cast p.property.one_lt) hs0 hs1 ht0 ht1
  have hg1 (p : Nat.Primes) : 1 ≤ g p := (hf1 p).trans (hfg p)
  have hP : (∏ p∈P,f p) ≤ ∏ p∈P,g p := Finset.prod_le_prod (fun p _ => (by norm_num : (0:ℝ)≤1).trans (hf1 p)) (fun p _ => hfg p)
  apply hP.trans
  apply ge_of_tendsto (rankin_coupled_comparison_hasProd_sparse s t hs0 ht0 hst)
  exact Filter.eventually_atTop.mpr ⟨P,fun T hPT => Finset.prod_le_prod_of_subset_of_one_le hPT
    (fun p _ => (by norm_num : (0:ℝ)≤1).trans (hg1 p)) (fun p _ _ => hg1 p)⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def rankinCoupledMomentWeightSparse (s t : ℝ) (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)^2*(n : ℝ)^(-s-t)/
    (∏ p∈n.primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))

lemma rankinCoupledMomentWeightSparse_nonneg (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (n : ℕ) :
    0 ≤ rankinCoupledMomentWeightSparse s t n := by
  apply div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hy : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hz : (p : ℝ)^(-t)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hi := Real.rpow_nonneg (Nat.cast_nonneg p) (-1)
  exact mul_nonneg (by linarith) (by linarith)

lemma rankinCoupledMomentWeightSparse_mul (s t : ℝ) {m n : ℕ} (hc : Nat.Coprime m n) :
    rankinCoupledMomentWeightSparse s t (m*n)=rankinCoupledMomentWeightSparse s t m*rankinCoupledMomentWeightSparse s t n := by
  have hP : (∏ p∈(m*n).primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))=
      (∏ p∈m.primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))*
      (∏ p∈n.primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))) := by
    rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
  dsimp [rankinCoupledMomentWeightSparse]
  rw [isMultiplicative_moebius.map_mul_of_coprime hc,Int.cast_mul,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity),hP]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma rankinCoupledMomentWeightSparse_prime_tail (s t : ℝ) (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) :
    rankinCoupledMomentWeightSparse s t (p^k)=0 := by
  have hmu : moebius (p^k)=0 := moebius_eq_zero_of_not_squarefree (by
    rw [squarefree_pow_iff hp.ne_one (by omega)]
    simp only [not_and_or]
    exact Or.inr (by omega))
  simp [rankinCoupledMomentWeightSparse,hmu]

lemma rankinCoupledMomentWeightSparse_prime_series (s t : ℝ) (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun k : ℕ => ‖rankinCoupledMomentWeightSparse s t (p^k)‖) ∧
      (∑' k : ℕ,rankinCoupledMomentWeightSparse s t (p^k))=
        1+(p : ℝ)^(-s-t)/((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))) := by
  constructor
  · apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro k hk
    rw [rankinCoupledMomentWeightSparse_prime_tail s t p k hp (by simpa only [Finset.mem_range,not_lt] using hk),norm_zero]
  · rw [tsum_eq_sum (s := Finset.range 2) (fun k hk => rankinCoupledMomentWeightSparse_prime_tail s t p k hp (by simpa only [Finset.mem_range,not_lt] using hk))]
    simp [Finset.sum_range_succ,rankinCoupledMomentWeightSparse,hp,moebius_apply_prime hp]

theorem rankin_coupled_moment_bound_sparse (s t : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    Summable (rankinCoupledMomentWeightSparse s t) ∧
      (∑' n : ℕ,rankinCoupledMomentWeightSparse s t n) ≤
        ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
          ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := by
  have hs : 0 < s := by linarith
  have ht : 0 < t := by linarith
  apply nonnegative_multiplicative_summable_of_local_product_bound (rankinCoupledMomentWeightSparse s t)
    (by simp [rankinCoupledMomentWeightSparse]) (by simp [rankinCoupledMomentWeightSparse])
    (rankinCoupledMomentWeightSparse_nonneg s t hs ht) (fun {_ _} hc => rankinCoupledMomentWeightSparse_mul s t hc)
    (fun {p} hp => (rankinCoupledMomentWeightSparse_prime_series s t p hp).1)
  intro S
  have h := rankin_coupled_finite_prime_product_upper_sparse (S.subtype Nat.Prime) s t hs0 hs1 ht0 ht1 hst
  have h' : (∏ p∈S with Nat.Prime p,(1+(p : ℝ)^(-s-t)/
      ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
        ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := by
    exact (Finset.prod_subtype_eq_prod_filter (s := S) (p := Nat.Prime) (fun p : ℕ =>
      (1+(p : ℝ)^(-s-t)/((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))))).symm.trans_le h
  calc
    _ = ∏ p∈S with Nat.Prime p,(1+(p : ℝ)^(-s-t)/
      ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (rankinCoupledMomentWeightSparse_prime_series s t p (Finset.mem_filter.mp hp).2).2
    _ ≤ _ := h'

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

theorem rankin_coupled_positive_divisor_series_certificate_sparse (s t : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    let f : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ)^2*(n : ℝ)^(-s-t)/
      (∏ p∈n.primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))
    let C : ℝ := ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
      ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ)))
    Summable f ∧ (∑' n : ℕ,f n) ≤ C ∧ ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n) ≤ C := by
  dsimp only
  have h := rankin_coupled_moment_bound_sparse s t hs0 hs1 ht0 ht1 hst
  refine ⟨h.1,h.2,?_⟩
  intro Y
  exact (h.1.sum_le_tsum _ (fun n _ => rankinCoupledMomentWeightSparse_nonneg s t (by linarith) (by linarith) n)).trans h.2

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

lemma rankin_sharp_factor_pos (q : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < rankinSharpCoprimeFactor q s := by
  unfold rankinSharpCoprimeFactor
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hmul := mul_pos (by linarith : (0 : ℝ) < p) (by linarith : 0 < 1-(p : ℝ)^(-s))
  exact div_pos (by linarith) (by nlinarith)

lemma rankin_sharp_factor_mul (m n : ℕ) (s : ℝ) (hc : Nat.Coprime m n) :
    rankinSharpCoprimeFactor (m*n) s =
      rankinSharpCoprimeFactor m s * rankinSharpCoprimeFactor n s := by
  unfold rankinSharpCoprimeFactor
  rw [hc.primeFactors_mul, Finset.prod_union hc.disjoint_primeFactors]

lemma rankin_shifted_local_product_pos (d : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < ∏ p∈d.primeFactors, (1-(p : ℝ)^(-s)+(p : ℝ)^(-1 : ℝ)) := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hi := Real.rpow_nonneg (Nat.cast_nonneg p) (-1)
  linarith

lemma rankin_sharp_factor_squarefree (d : ℕ) (hd : Squarefree d) (s : ℝ) :
    rankinSharpCoprimeFactor d s =
      (∏ p∈d.primeFactors, ((p : ℝ)+1)) /
        ((d : ℝ)*(∏ p∈d.primeFactors, (1-(p : ℝ)^(-s)+(p : ℝ)^(-1 : ℝ)))) := by
  have hprod : (∏ p∈d.primeFactors, (p : ℝ)) = (d : ℝ) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_of_squarefree hd)
  have hden : (∏ p∈d.primeFactors, ((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s))) =
      (d : ℝ)*(∏ p∈d.primeFactors, (1-(p : ℝ)^(-s)+(p : ℝ)^(-1 : ℝ))) := by
    rw [← hprod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [Real.rpow_neg_one]
    field_simp
    <;> ring
  unfold rankinSharpCoprimeFactor
  rw [Finset.prod_div_distrib, hden]

lemma rankin_sharp_coupled_weight_identity (d : ℕ) (hd : 1 ≤ d) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) :
    |((moebius d : ℤ) : ℝ)| / (∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
      (d : ℝ)^(2-s-t) * rankinSharpCoprimeFactor d s * rankinSharpCoprimeFactor d t =
        rankinCoupledMomentWeightSparse s t d := by
  by_cases hsf : Squarefree d
  · have hmuabs : |((moebius d : ℤ) : ℝ)| = 1 := by
      exact_mod_cast abs_moebius_eq_one_of_squarefree hsf
    have hmusq : ((moebius d : ℤ) : ℝ)^2 = 1 := by
      nlinarith [sq_abs (((moebius d : ℤ) : ℝ))]
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd
    have hsp := mobius_sigma_product_pos d
    have hbs := rankin_shifted_local_product_pos d s hs
    have hbt := rankin_shifted_local_product_pos d t ht
    have hpow : (d : ℝ)^(2-s-t) = (d : ℝ)^2*(d : ℝ)^(-s-t) := by
      rw [show 2-s-t = (2 : ℝ)+(-s-t) by ring, Real.rpow_add hdp, Real.rpow_two]
    rw [rankin_sharp_factor_squarefree d hsf s, rankin_sharp_factor_squarefree d hsf t]
    dsimp [rankinCoupledMomentWeightSparse]
    rw [hmuabs, hmusq, hpow, Finset.prod_mul_distrib]
    field_simp [ne_of_gt hdp, ne_of_gt hsp, ne_of_gt hbs, ne_of_gt hbt]
    <;> ring
  · simp [moebius_eq_zero_of_not_squarefree hsf, rankinCoupledMomentWeightSparse]

theorem rankin_sharp_coprime_coupled_weight_upper (q D : ℕ) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    let J : ℕ → ℝ → ℝ := fun n u =>
      ∏ p∈n.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u))
    (∑ d∈Icc 1 D, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (d : ℝ)^(2-s-t)*J (d*q) s*J (d*q) t else 0) ≤
      J q s*J q t *
        (((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
          ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))) := by
  have hs : 0 < s := by linarith
  have ht : 0 < t := by linarith
  dsimp only
  change (∑ d∈Icc 1 D, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (d : ℝ)^(2-s-t)*rankinSharpCoprimeFactor (d*q) s*rankinSharpCoprimeFactor (d*q) t else 0) ≤ _
  have heq : (∑ d∈Icc 1 D, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (d : ℝ)^(2-s-t)*rankinSharpCoprimeFactor (d*q) s*rankinSharpCoprimeFactor (d*q) t else 0) =
      (rankinSharpCoprimeFactor q s*rankinSharpCoprimeFactor q t)*
        (∑ d∈Icc 1 D, if Nat.Coprime d q then rankinCoupledMomentWeightSparse s t d else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hdI
    by_cases hc : Nat.Coprime d q
    · simp only [if_pos hc]
      rw [rankin_sharp_factor_mul d q s hc, rankin_sharp_factor_mul d q t hc,
        ← rankin_sharp_coupled_weight_identity d (Finset.mem_Icc.mp hdI).1 s t hs ht]
      ring
    · simp only [if_neg hc, mul_zero]
  rw [heq]
  have hfactor : 0 ≤ rankinSharpCoprimeFactor q s*rankinSharpCoprimeFactor q t :=
    mul_nonneg (rankin_sharp_factor_pos q s hs).le (rankin_sharp_factor_pos q t ht).le
  apply mul_le_mul_of_nonneg_left _ hfactor
  have hfull := (rankin_coupled_positive_divisor_series_certificate_sparse s t hs0 hs1 ht0 ht1 hst).2.2 D
  apply le_trans _ hfull
  apply Finset.sum_le_sum
  intro d hd
  by_cases hc : Nat.Coprime d q
  · simp only [if_pos hc, rankinCoupledMomentWeightSparse, le_refl]
  · simp only [if_neg hc]
    exact rankinCoupledMomentWeightSparse_nonneg s t hs ht d

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def rankinSingleZetaConstant (s : ℝ) : ℝ :=
  ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/
    (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))

noncomputable def rankinCoupledZetaConstant (s t : ℝ) : ℝ :=
  ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
    ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))

noncomputable def rankinSharpCoupledOuter (q Y : ℕ) (s t : ℝ) : ℝ :=
  ∑ d∈Icc 1 Y, if Nat.Coprime d q then
    |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
      (d : ℝ)^(2-s-t)*rankinSharpCoprimeFactor (d*q) s*rankinSharpCoprimeFactor (d*q) t else 0

lemma rankin_single_zeta_constant_nonneg (s : ℝ) : 0 ≤ rankinSingleZetaConstant s := by
  unfold rankinSingleZetaConstant
  exact div_nonneg (mul_nonneg
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma rankin_sharp_coupled_outer_upper (q Y : ℕ) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    rankinSharpCoupledOuter q Y s t ≤
      rankinSharpCoprimeFactor q s*rankinSharpCoprimeFactor q t*rankinCoupledZetaConstant s t :=
  rankin_sharp_coprime_coupled_weight_upper q Y s t hs0 hs1 ht0 ht1 hst

theorem mobius_sigma_coprime_divisor_energy_rankin_upper (q Y L : ℕ) (c s : ℝ)
    (hq : 1 ≤ q) (hY : 1 ≤ Y) (hL : 1 ≤ L) (hc : 0 ≤ c) (hs0 : 1/2 < s) (hs1 : s ≤ 1)
    (hM : ∀ N : ℕ, L ≤ N → |∑ a∈Icc 1 N, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ c) :
    let R : ℝ → ℝ := fun t =>
      (((∑' n : ℕ,(n : ℝ)^(-t-1))*(∑' n : ℕ,(n : ℝ)^(-2*t-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-t)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))
    let P : ℝ := ((2*(L : ℝ))/Y)^(1-s)
    (∑ d∈Icc 1 Y, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (∑ r∈Icc 1 (Y/d), if Nat.Coprime r (d*q) then
          ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0)^2 else 0) ≤
      c^2*(R 1)^2*C 1 1 + 2*c*P*R 1*R s*C 1 s + P^2*(R s)^2*C s s := by
  let K := rankinSingleZetaConstant
  let J := rankinSharpCoprimeFactor
  let P : ℝ := ((2*(L : ℝ))/Y)^(1-s)
  let w : ℕ → ℝ := fun d => |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2
  let f : ℕ → ℝ := fun d => ∑ r∈Icc 1 (Y/d), if Nat.Coprime r (d*q) then
    ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0
  let B : ℕ → ℝ := fun d => c*K 1*J (d*q) 1 + P*K s*(d : ℝ)^(1-s)*J (d*q) s
  have hs : 0 < s := by linarith
  have hK1 : 0 ≤ K 1 := rankin_single_zeta_constant_nonneg 1
  have hKs : 0 ≤ K s := rankin_single_zeta_constant_nonneg s
  have hP : 0 ≤ P := by positivity
  have hw (d : ℕ) : 0 ≤ w d := by dsimp [w]; positivity
  have hB (d : ℕ) : 0 ≤ B d := by
    have hJ1 := (rankin_sharp_factor_pos (d*q) 1 (by norm_num)).le
    have hJs := (rankin_sharp_factor_pos (d*q) s hs).le
    dsimp only [B, J]
    positivity
  have hb (d : ℕ) (hdI : d∈Icc 1 Y) : |f d| ≤ B d := by
    have hd : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
    have hKd : 1 ≤ Y/d := (Nat.le_div_iff_mul_le (by omega)).mpr
      (by simpa using (Finset.mem_Icc.mp hdI).2)
    have hdn : 0 < d := by omega
    have hYnat : Y ≤ 2*d*(Y/d) := by
      have hi := Nat.lt_mul_div_succ Y hdn
      nlinarith
    have hYp : (0 : ℝ) < Y := by exact_mod_cast hY
    have hKp : (0 : ℝ) < (Y/d : ℕ) := by exact_mod_cast hKd
    have hYr : (Y : ℝ) ≤ 2*(d : ℝ)*(Y/d : ℕ) := by exact_mod_cast hYnat
    have hbase : (L : ℝ)/(Y/d : ℕ) ≤ ((2*(L : ℝ))/Y)*d := by
      have hi : (L : ℝ)/(Y/d : ℕ) ≤ (2*(L : ℝ)*d)/Y := by
        apply (div_le_div_iff₀ hKp hYp).mpr
        have hm := mul_le_mul_of_nonneg_left hYr (Nat.cast_nonneg L)
        nlinarith
      convert hi using 1 <;> ring
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (L : ℝ)/(Y/d : ℕ)) hbase (by linarith : 0 ≤ 1-s)
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg d)] at hpow
    have hJ := (rankin_sharp_factor_pos (d*q) s hs).le
    have hi := mobius_sigma_coprime_rankin_decay_sharp_upper (d*q) (Y/d) L c s
      (by nlinarith) hKd hL hc hs0.le hs1 hM
    change |f d| ≤ c*(K 1*J (d*q) 1) + ((L : ℝ)/(Y/d : ℕ))^(1-s)*(K s*J (d*q) s) at hi
    simp only [← mul_assoc] at hi
    apply hi.trans
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hKs) hJ
    dsimp only [B, J, P]
    nlinarith
  dsimp only
  change (∑ d∈Icc 1 Y, if Nat.Coprime d q then w d*(f d)^2 else 0) ≤
    c^2*(K 1*J q 1)^2*rankinCoupledZetaConstant 1 1 +
      2*c*P*(K 1*J q 1)*(K s*J q s)*rankinCoupledZetaConstant 1 s +
      P^2*(K s*J q s)^2*rankinCoupledZetaConstant s s
  have hsum : (∑ d∈Icc 1 Y, if Nat.Coprime d q then w d*(f d)^2 else 0) ≤
      ∑ d∈Icc 1 Y, if Nat.Coprime d q then w d*(B d)^2 else 0 := by
    apply Finset.sum_le_sum
    intro d hd
    by_cases hdq : Nat.Coprime d q
    · simp only [if_pos hdq]
      apply mul_le_mul_of_nonneg_left _ (hw d)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f d)) (hB d)).mpr (hb d hd)
    · simp only [if_neg hdq, le_refl]
  have hexpand : (∑ d∈Icc 1 Y, if Nat.Coprime d q then w d*(B d)^2 else 0) =
      c^2*(K 1)^2*rankinSharpCoupledOuter q Y 1 1 +
      2*c*P*K 1*K s*rankinSharpCoupledOuter q Y 1 s +
      P^2*(K s)^2*rankinSharpCoupledOuter q Y s s := by
    unfold rankinSharpCoupledOuter
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdq : Nat.Coprime d q
    · simp only [if_pos hdq]
      rw [show (2 : ℝ)-1-1 = 0 by ring, Real.rpow_zero,
        show (2 : ℝ)-1-s = 1-s by ring, show (2 : ℝ)-s-s = (1-s)*2 by ring,
        Real.rpow_mul (Nat.cast_nonneg d), Real.rpow_two]
      dsimp [w, B, J]
      ring
    · simp only [if_neg hdq, mul_zero, add_zero]
  have hm11 := rankin_sharp_coupled_outer_upper q Y 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hm1s := rankin_sharp_coupled_outer_upper q Y 1 s (by norm_num) (by norm_num) hs0.le hs1 (by linarith)
  have hmss := rankin_sharp_coupled_outer_upper q Y s s hs0.le hs1 hs0.le hs1 (by linarith)
  apply hsum.trans
  rw [hexpand]
  have hbound := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hm11 (by positivity : 0 ≤ c^2*(K 1)^2))
    (mul_le_mul_of_nonneg_left hm1s (by positivity : 0 ≤ 2*c*P*K 1*K s)))
    (mul_le_mul_of_nonneg_left hmss (by positivity : 0 ≤ P^2*(K s)^2))
  apply hbound.trans_eq
  dsimp [J]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_sigma_coprime_real_two_power_energy_upper_complete
    (q : ℕ) (X L T a b s t : ℝ)
    (hq : 1 ≤ q) (hX : 1 ≤ X) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 1/2 < s) (hs1 : s ≤ 1)
    (ht0 : 1/2 < t) (ht1 : t ≤ 1)
    (hM : ∀ z : ℝ, 1 ≤ z → z ≤ X →
      |∑ r∈Icc 1 ⌊z⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/z)^(1-s)+b*(T/z)^(1-t)) :
    let R : ℝ → ℝ := fun u =>
      (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))
    let P : ℝ := (L/X)^(1-s)
    let Z : ℝ := (T/X)^(1-t)
    (∑ d∈Icc 1 ⌊X⌋₊, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (∑ r∈Icc 1 ⌊X/(d : ℝ)⌋₊, if Nat.Coprime r (d*q) then
          ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0)^2 else 0) ≤
      a^2*P^2*(R s)^2*C s s + 2*a*b*P*Z*R s*R t*C s t + b^2*Z^2*(R t)^2*C t t := by
  let K := rankinSingleZetaConstant
  let J := rankinSharpCoprimeFactor
  let P := (L/X)^(1-s)
  let Z := (T/X)^(1-t)
  let Y := ⌊X⌋₊
  let w : ℕ → ℝ := fun d => |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2
  let f : ℕ → ℝ := fun d => ∑ r∈Icc 1 ⌊X/(d : ℝ)⌋₊, if Nat.Coprime r (d*q) then
    ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)) else 0
  let B : ℕ → ℝ := fun d => a*P*K s*(d : ℝ)^(1-s)*J (d*q) s +
    b*Z*K t*(d : ℝ)^(1-t)*J (d*q) t
  have hXp : 0 < X := by linarith
  have hs : 0 < s := by linarith
  have ht : 0 < t := by linarith
  have hKs : 0 ≤ K s := rankin_single_zeta_constant_nonneg s
  have hKt : 0 ≤ K t := rankin_single_zeta_constant_nonneg t
  have hP : 0 ≤ P := by positivity
  have hZ : 0 ≤ Z := by positivity
  have hw (d : ℕ) : 0 ≤ w d := by dsimp [w];positivity
  have hB (d : ℕ) : 0 ≤ B d := by
    have hJs := (rankin_sharp_factor_pos (d*q) s hs).le
    have hJt := (rankin_sharp_factor_pos (d*q) t ht).le
    dsimp only [B,J]
    positivity
  have hbound (d : ℕ) (hdI : d∈Icc 1 Y) : |f d| ≤ B d := by
    have hd : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd
    have hdX : (d : ℝ) ≤ X := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hdI).2)
      (Nat.floor_le hXp.le)
    have hin1 : 1 ≤ X/d := (le_div_iff₀ hdp).mpr (by simpa using hdX)
    have hinX : X/d ≤ X := (div_le_iff₀ hdp).mpr (by
      have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith)
    have hi := mobius_sigma_coprime_real_two_power_rankin_upper (d*q) (X/d) L T a b s t
      (by nlinarith) hin1 hL hT ha hb hs0.le hs1 ht0.le ht1
      (fun z hz hzx => hM z hz (hzx.trans hinX))
    change |f d| ≤ a*(L/(X/d))^(1-s)*(K s*J (d*q) s) +
      b*(T/(X/d))^(1-t)*(K t*J (d*q) t) at hi
    have hLP : (L/(X/d))^(1-s)=P*(d : ℝ)^(1-s) := by
      dsimp only [P]
      rw [show L/(X/d)=(L/X)*d by field_simp <;> ring, Real.mul_rpow (div_nonneg hL hXp.le) hdp.le]
    have hTZ : (T/(X/d))^(1-t)=Z*(d : ℝ)^(1-t) := by
      dsimp only [Z]
      rw [show T/(X/d)=(T/X)*d by field_simp <;> ring, Real.mul_rpow (div_nonneg hT hXp.le) hdp.le]
    apply hi.trans_eq
    rw [hLP,hTZ]
    dsimp only [B]
    ring
  dsimp only
  change (∑ d∈Icc 1 Y,if Nat.Coprime d q then w d*(f d)^2 else 0) ≤
    a^2*P^2*(K s*J q s)^2*rankinCoupledZetaConstant s s +
    2*a*b*P*Z*(K s*J q s)*(K t*J q t)*rankinCoupledZetaConstant s t +
    b^2*Z^2*(K t*J q t)^2*rankinCoupledZetaConstant t t
  have hsum : (∑ d∈Icc 1 Y,if Nat.Coprime d q then w d*(f d)^2 else 0) ≤
      ∑ d∈Icc 1 Y,if Nat.Coprime d q then w d*(B d)^2 else 0 := by
    apply Finset.sum_le_sum
    intro d hd
    by_cases hdq : Nat.Coprime d q
    · simp only [if_pos hdq]
      apply mul_le_mul_of_nonneg_left _ (hw d)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f d)) (hB d)).mpr (hbound d hd)
    · simp only [if_neg hdq,le_refl]
  have hexpand : (∑ d∈Icc 1 Y,if Nat.Coprime d q then w d*(B d)^2 else 0) =
      a^2*P^2*(K s)^2*rankinSharpCoupledOuter q Y s s +
      2*a*b*P*Z*K s*K t*rankinSharpCoupledOuter q Y s t +
      b^2*Z^2*(K t)^2*rankinSharpCoupledOuter q Y t t := by
    unfold rankinSharpCoupledOuter
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdq : Nat.Coprime d q
    · simp only [if_pos hdq]
      have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      rw [show (2 : ℝ)-s-s=(1-s)*2 by ring,Real.rpow_mul hdp.le,Real.rpow_two,
        show (2 : ℝ)-s-t=(1-s)+(1-t) by ring,Real.rpow_add hdp,
        show (2 : ℝ)-t-t=(1-t)*2 by ring,Real.rpow_mul hdp.le,Real.rpow_two]
      dsimp [w,B,J]
      ring
    · simp only [if_neg hdq,mul_zero,add_zero]
  have hmss := rankin_sharp_coupled_outer_upper q Y s s hs0.le hs1 hs0.le hs1 (by linarith)
  have hmst := rankin_sharp_coupled_outer_upper q Y s t hs0.le hs1 ht0.le ht1 (by linarith)
  have hmtt := rankin_sharp_coupled_outer_upper q Y t t ht0.le ht1 ht0.le ht1 (by linarith)
  apply hsum.trans
  rw [hexpand]
  have hi := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hmss (by positivity : 0 ≤ a^2*P^2*(K s)^2))
    (mul_le_mul_of_nonneg_left hmst (by positivity : 0 ≤ 2*a*b*P*Z*K s*K t)))
    (mul_le_mul_of_nonneg_left hmtt (by positivity : 0 ≤ b^2*Z^2*(K t)^2))
  apply hi.trans_eq
  ring

end Helfgott
end

open Helfgott Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
theorem solution 
    (q : ℕ) (X L T a b s t : ℝ)
    (hq : 1 ≤ q) (hX : 1 ≤ X) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 1/2 < s) (hs1 : s ≤ 1)
    (ht0 : 1/2 < t) (ht1 : t ≤ 1)
    (hM : ∀ z : ℝ, 1 ≤ z → z ≤ X →
      |∑ r∈Icc 1 ⌊z⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/z)^(1-s)+b*(T/z)^(1-t)) :
    let R : ℝ → ℝ := fun u =>
      (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))
    let P : ℝ := (L/X)^(1-s)
    let Z : ℝ := (T/X)^(1-t)
    (∑ d∈Icc 1 ⌊X⌋₊, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (∑ r∈Icc 1 ⌊X/(d : ℝ)⌋₊, if Nat.Coprime r (d*q) then
          ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0)^2 else 0) ≤
      a^2*P^2*(R s)^2*C s s + 2*a*b*P*Z*R s*R t*C s t + b^2*Z^2*(R t)^2*C t t := Helfgott.mobius_sigma_coprime_real_two_power_energy_upper_complete q X L T a b s t hq hX hL hT ha hb hs0 hs1 ht0 ht1 hM
#print axioms solution
