-- Prove2me | solution 1 for Helfgott.mobius_sigma_coprime_pair_positive_majorant
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T16:09:31.710029+00:00
-- url     : https://prove2.me/submissions/e53179b1-133c-4bb2-b55c-e986456d3b95

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt

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

theorem mobius_sigma_coprime_pair_quadratic_bound (q Y : ℕ) :
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

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_sigma_coprime_pair_positive_majorant_complete (q Y : ℕ) (F : ℕ→ℝ)
    (hF : ∀ N≤Y,|∑ a∈Finset.Icc 1 N,((moebius a : ℤ) : ℝ)/(a : ℝ)|≤F N) :
    let sigma : ℕ→ℝ := fun n => ∏ p∈n.primeFactors,((p : ℝ)+1)
    let T : ℕ→ℕ→ℝ := fun Q N => ∑ e∈Finset.Icc 1 N,if Nat.Coprime e Q then
      (((moebius e : ℤ) : ℝ)^2/((e : ℝ)*sigma e))*
        (∑ b∈Finset.Icc 1 (N/e),if (∀ p∈b.primeFactors,p∣e*Q) then
          (1/(b : ℝ))*F ((N/e)/b) else 0) else 0
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
        (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t) else 0|≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(sigma d)^2)*(T (d*q) (Y/d))^2 else 0 := by
  dsimp only
  apply (mobius_sigma_coprime_pair_quadratic_bound q Y).trans
  apply Finset.sum_le_sum
  intro d hd
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc,if_pos hc]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (abs_nonneg _) (sq_nonneg _))
    have hb := mobius_sigma_coprime_positive_majorant (d*q) (Y/d) F
      (fun N hN => hF N (hN.trans (Nat.div_le_self _ _)))
    have hn := (abs_nonneg _).trans hb
    exact sq_le_sq.mpr (by simpa only [mobiusSigmaWeight,abs_of_nonneg hn] using hb)
  · rw [if_neg hc,if_neg hc]

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (q Y : ℕ) (F : ℕ→ℝ)
    (hF : ∀ N≤Y,|∑ a∈Finset.Icc 1 N,((moebius a : ℤ) : ℝ)/(a : ℝ)|≤F N) :
    let sigma : ℕ→ℝ := fun n => ∏ p∈n.primeFactors,((p : ℝ)+1)
    let T : ℕ→ℕ→ℝ := fun Q N => ∑ e∈Finset.Icc 1 N,if Nat.Coprime e Q then
      (((moebius e : ℤ) : ℝ)^2/((e : ℝ)*sigma e))*
        (∑ b∈Finset.Icc 1 (N/e),if (∀ p∈b.primeFactors,p∣e*Q) then
          (1/(b : ℝ))*F ((N/e)/b) else 0) else 0
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
        (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t) else 0|≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(sigma d)^2)*(T (d*q) (Y/d))^2 else 0 := Helfgott.mobius_sigma_coprime_pair_positive_majorant_complete q Y F hF

#print axioms solution
