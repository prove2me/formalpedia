-- Prove2me | solution 1 for Helfgott.coprime_mobius_sigma_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T21:43:18.40661+00:00
-- url     : https://prove2.me/submissions/9fe08af8-5c34-4e40-9778-d56bc7637755

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_Helfgott_VaughanData
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.ZetaValues
section
/- Retained accepted Prove2Me proof d7d657d4-5077-45b3-9cc5-08a726ff8190 by raresbuhai, Apache 2.0. -/

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace HelfgottSigma

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

end HelfgottSigma
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace HelfgottSigma

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

end HelfgottSigma
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace HelfgottSigma

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

end HelfgottSigma
end

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace HelfgottSigma

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

end HelfgottSigma
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace HelfgottSigma

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

end HelfgottSigma
end


end

section
/- Arithmetic support identities retained from accepted Prove2Me submission
4b19f26e-e6f8-4a14-8cf6-e0ea33b44440 by raresbuhai (Apache 2.0). -/

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace HelfgottQuadratic

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

end HelfgottQuadratic
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace HelfgottQuadratic

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


end HelfgottQuadratic
end

end

section
/- Finite hyperbola reindexing retained from accepted Prove2Me submission
4b19f26e-e6f8-4a14-8cf6-e0ea33b44440 by raresbuhai (Apache 2.0). -/
open Finset
open scoped BigOperators
namespace HelfgottQuadratic
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


end HelfgottQuadratic

end

section
/- Arithmetic energy proofs retained from accepted Prove2Me submission
dc167013-7b1b-47a5-bd68-36e63ad77223 by raresbuhai, Apache 2.0. -/
open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace HelfgottQuadratic
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


lemma arithmeticTail_zero_of_le (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : n ≤ U) :
    arithmeticTail U f n = 0 := by
  change f n-(if n ≤ U then f n else 0) = 0
  simp [hn]

lemma arithmeticTail_self_of_gt (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : U < n) :
    arithmeticTail U f n = f n := by
  change f n-(if n ≤ U then f n else 0) = f n
  simp [not_le_of_gt hn]

lemma vaughan_bilinear_coefficient_zero (U n : ℕ) (hn : n ≤ U) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdn : d ≤ n := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.mem_divisors.mp hd).1
  exact arithmeticTail_zero_of_le U d _ (hdn.trans hn)

lemma vaughan_bilinear_coefficient_short_moebius (U n : ℕ) (hn : n ≠ 1) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n =
      -(∑ d ∈ n.divisors.filter (fun d => d ≤ U), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  have he : arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta =
      1-arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta := by
    unfold arithmeticTail
    rw [sub_mul,ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [he]
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,
    ArithmeticFunction.one_apply_ne hn,zero_add]
  rw [ArithmeticFunction.coe_mul_zeta_apply,Finset.sum_filter]
  congr 1


lemma short_moebius_divisor_sum (U n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors.filter (fun d => d ≤ U),((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 U,if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
  have he : n.divisors.filter (fun d => d ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hdU⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,hdU⟩,hd⟩
    · rintro ⟨⟨hdpos,hdU⟩,hd⟩
      exact ⟨⟨hd,hn.ne'⟩,hdU⟩
  rw [he,Finset.sum_filter]

lemma vaughan_mobius_energy_pointwise (U n : ℕ) (hU : 1 ≤ U) (hn : 0 < n) :
    ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n)^2 =
      (∑ d ∈ Finset.Icc 1 U,if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)^2-
      (if n=1 then 1 else 0) := by
  by_cases hn1 : n=1
  · subst n
    rw [vaughan_bilinear_coefficient_zero U 1 hU]
    have hs : (∑ d ∈ Finset.Icc 1 U,if d ∣ 1 then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) = 1 := by
      rw [←short_moebius_divisor_sum U 1 (by norm_num)]
      rw [Nat.divisors_one,Finset.filter_singleton]
      simp [hU]
    rw [hs]
    norm_num
  · rw [vaughan_bilinear_coefficient_short_moebius U n hn1,short_moebius_divisor_sum U n hn,if_neg hn1]
    ring

theorem vaughan_mobius_tail_square_energy (U M : ℕ) (hU : 1 ≤ U) :
    (∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)*
        ((M/(Nat.lcm d e) : ℕ) : ℝ))-(if 1 ≤ M then 1 else 0) := by
  have hs : (∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      (∑ m ∈ Finset.Icc 1 M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) := by
    apply Finset.sum_subset
    · intro m hm
      exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hm).1;omega,(Finset.mem_Icc.mp hm).2⟩
    · intro m hm hnot
      have hmU : m ≤ U := by
        have hml := (Finset.mem_Icc.mp hm).1
        have hmh := (Finset.mem_Icc.mp hm).2
        have hnot' : ¬(U+1 ≤ m ∧ m ≤ M) := by simpa only [Finset.mem_Icc] using hnot
        omega
      rw [vaughan_bilinear_coefficient_zero U m hmU]
      simp
  rw [hs]
  have he : (∑ m ∈ Finset.Icc 1 M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      ∑ m ∈ Finset.Icc 1 M,
        ((∑ d ∈ Finset.Icc 1 U,if d ∣ m then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)^2-
          (if m=1 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact vaughan_mobius_energy_pointwise U m hU (Finset.mem_Icc.mp hm).1
  rw [he,Finset.sum_sub_distrib,finite_divisor_weight_square_energy]
  congr 1
  simp only [Finset.sum_ite_eq',Finset.mem_Icc]
  simp


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


theorem vaughan_mobius_tail_energy_asymptotic (U M : ℕ) (hU : 1 ≤ U) :
    (0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ)) ∧
    |(∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2)+
      (if 1 ≤ M then 1 else 0)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))| ≤ (U : ℝ)^2 := by
  refine ⟨finite_divisor_weight_leading_quadratic_nonneg U _,?_⟩
  have hsum : (∑ d ∈ Finset.Icc 1 U,|((ArithmeticFunction.moebius d : ℤ) : ℝ)|) ≤ (U : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 U,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      _ = _ := by simp
  have h := finite_divisor_weight_square_energy_approximation M U (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
  have he := vaughan_mobius_tail_square_energy U M hU
  have hfull := finite_divisor_weight_square_energy M U (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
  rw [hfull] at h
  rw [he,sub_add_cancel]
  refine h.trans ?_
  nlinarith [Finset.sum_nonneg (fun d (_ : d ∈ Finset.Icc 1 U) => abs_nonneg (((ArithmeticFunction.moebius d : ℤ) : ℝ)))]


theorem vonMangoldt_square_interval_energy (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    (∑ d ∈ Finset.Ico A B,(vonMangoldt d)^2) ≤
      Real.log (B : ℝ)*(Real.log 4*(B : ℝ)+2*Real.sqrt (B : ℝ)*Real.log (B : ℝ)) := by
  have hBR : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBR
  have hpoint (d : ℕ) (hd : d ∈ Finset.Ico A B) :
      (vonMangoldt d)^2 ≤ Real.log (B : ℝ)*vonMangoldt d := by
    have hdpos : (0:ℝ)<d := by exact_mod_cast (show 0<d from by have := (Finset.mem_Ico.mp hd).1;omega)
    have hdB : (d : ℝ) ≤ B := by exact_mod_cast (Finset.mem_Ico.mp hd).2.le
    have hl := (vonMangoldt_le_log (n := d)).trans (Real.log_le_log hdpos hdB)
    nlinarith [vonMangoldt_nonneg (n := d)]
  have hsubset : Finset.Ico A B ⊆ Finset.Icc 1 B := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨hA.trans (Finset.mem_Ico.mp hd).1,(Finset.mem_Ico.mp hd).2.le⟩
  have hpsi : (∑ d ∈ Finset.Icc 1 B,vonMangoldt d) = Chebyshev.psi (B : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    apply Finset.sum_subset
    · intro d hd
      exact Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hd).2⟩
    · intro d hd hnot
      have hd0 : d=0 := by
        have hdB := (Finset.mem_Icc.mp hd).2
        have hnot' : ¬(1 ≤ d ∧ d ≤ B) := by simpa only [Finset.mem_Icc] using hnot
        omega
      subst d
      simp
  calc
    _ ≤ ∑ d ∈ Finset.Ico A B,Real.log (B : ℝ)*vonMangoldt d := Finset.sum_le_sum hpoint
    _ = Real.log (B : ℝ)*(∑ d ∈ Finset.Ico A B,vonMangoldt d) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log (B : ℝ)*(∑ d ∈ Finset.Icc 1 B,vonMangoldt d) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => vonMangoldt_nonneg)) hlogB
    _ = Real.log (B : ℝ)*Chebyshev.psi (B : ℝ) := by rw [hpsi]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Chebyshev.psi_le hBR) hlogB


lemma vaughan_mobius_interval_energy_upper (U C D : ℕ) (hU : 1 ≤ U) (hC : U+1 ≤ C) :
    (∑ m ∈ Finset.Ico C D,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) ≤
      (D : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))+(U : ℝ)^2 := by
  have hsubset : Finset.Ico C D ⊆ Finset.Icc (U+1) D := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨hC.trans (Finset.mem_Ico.mp hm).1,(Finset.mem_Ico.mp hm).2.le⟩
  have h := (vaughan_mobius_tail_energy_asymptotic U D hU).2
  have hupper := (le_abs_self _).trans h
  have hδ : (0:ℝ) ≤ (if 1 ≤ D then 1 else 0) := by split_ifs <;> norm_num
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m _ _ => sq_nonneg _)).trans ?_
  linarith


end HelfgottQuadratic

end

section

open Finset ArithmeticFunction
open scoped BigOperators
namespace HelfgottQuadratic

theorem coprime_mobius_floor_identity (q N : ℕ) :
    (∑ d ∈ Icc 1 N, coprimeMobiusAF q d*((N/d:ℕ):ℝ)) =
      ∑ n ∈ Icc 1 N, primeSupportedAF q n := by
  have hh := finite_positive_divisor_reindex N (fun d _ => coprimeMobiusAF q d)
  have hpoint : ∀ n, (∑ d ∈ n.divisors, coprimeMobiusAF q d) = primeSupportedAF q n := by
    intro n
    rw [← ArithmeticFunction.coe_mul_zeta_apply,coprimeMobiusAF_zeta_eq_primeSupported]
  simp_rw [hpoint] at hh
  rw [hh]
  apply sum_congr rfl
  intro d hd
  simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
  ring

theorem prime_supported_coprime_complement (q n : ℕ) (hn : 1≤n) :
    0≤primeSupportedAF q n ∧
      primeSupportedAF q n+(if Nat.Coprime n q ∧ n≠1 then (1:ℝ) else 0) ≤ 1 := by
  rw [primeSupportedAF_apply_positive q n hn]
  have hdisjoint : (∀ p∈n.primeFactors, p∣q) → Nat.Coprime n q → n=1 := by
    intro hs hc
    by_contra hn1
    have hp := Nat.minFac_prime hn1
    have hpn := Nat.minFac_dvd n
    have hpf : n.minFac ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpn,by omega⟩
    exact (hp.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hpn hc)) (hs _ hpf)
  split_ifs <;> simp_all

theorem coprime_mobius_reciprocal_abs_le_one (q N : ℕ) :
    |∑ d ∈ Icc 1 N, if Nat.Coprime d q then ((moebius d:ℤ):ℝ)/(d:ℝ) else 0| ≤ 1 := by
  by_cases hN : N=0
  · subst N
    simp
  have hNp : 0<N := Nat.pos_of_ne_zero hN
  let delta : ℕ → ℝ := fun d => (N:ℝ)/(d:ℝ)-((N/d:ℕ):ℝ)
  have hd0 : ∀ d, 0≤delta d := fun d => sub_nonneg.mpr Nat.cast_div_le
  have hd1 : ∀ d, 0<d → delta d≤1 := by
    intro d hd
    have hh := nat_div_cast_error_le_one N d hd
    rw [abs_sub_comm,abs_of_nonneg (hd0 d)] at hh
    exact hh
  have he : (N:ℝ)*(∑ d ∈ Icc 1 N, if Nat.Coprime d q then ((moebius d:ℤ):ℝ)/(d:ℝ) else 0) =
      (∑ n ∈ Icc 1 N, primeSupportedAF q n)+∑ d ∈ Icc 1 N, coprimeMobiusAF q d*delta d := by
    rw [← coprime_mobius_floor_identity q N,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    dsimp [coprimeMobiusAF,delta]
    split_ifs <;> ring
  have herr : ∀ d ∈ Icc 1 N, |coprimeMobiusAF q d*delta d| ≤
      if Nat.Coprime d q ∧ d≠1 then (1:ℝ) else 0 := by
    intro d hd
    change |(if Nat.Coprime d q then ((moebius d:ℤ):ℝ) else 0)*delta d| ≤ _
    by_cases hdq : Nat.Coprime d q
    · by_cases hdone : d=1
      · subst d
        simp [delta]
      · have hboth : Nat.Coprime d q ∧ d≠1 := ⟨hdq,hdone⟩
        rw [if_pos hdq,if_pos hboth,abs_mul,abs_of_nonneg (hd0 d)]
        have hmu : |((moebius d:ℤ):ℝ)|≤1 := by exact_mod_cast abs_moebius_le_one (n:=d)
        exact mul_le_one₀ hmu (hd0 d) (hd1 d (mem_Icc.mp hd).1)
    · simp [hdq]
  have hbound : |(N:ℝ)*(∑ d ∈ Icc 1 N, if Nat.Coprime d q then ((moebius d:ℤ):ℝ)/(d:ℝ) else 0)| ≤ N := by
    rw [he]
    calc
      _ ≤ |∑ n ∈ Icc 1 N, primeSupportedAF q n|+|∑ d ∈ Icc 1 N, coprimeMobiusAF q d*delta d| := abs_add_le _ _
      _ ≤ (∑ n ∈ Icc 1 N, primeSupportedAF q n)+
          (∑ d ∈ Icc 1 N, if Nat.Coprime d q ∧ d≠1 then (1:ℝ) else 0) := by
        rw [abs_of_nonneg (sum_nonneg (fun n hn => (prime_supported_coprime_complement q n (mem_Icc.mp hn).1).1))]
        exact add_le_add le_rfl ((abs_sum_le_sum_abs _ _).trans (sum_le_sum herr))
      _ ≤ ∑ _n ∈ Icc 1 N, (1:ℝ) := by
        rw [← sum_add_distrib]
        exact sum_le_sum (fun n hn => (prime_supported_coprime_complement q n (mem_Icc.mp hn).1).2)
      _ = _ := by simp
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) N)] at hbound
  have hNpR : (0:ℝ)<N := by exact_mod_cast hNp
  nlinarith

end HelfgottQuadratic

end

section

open Finset ArithmeticFunction
open scoped BigOperators
namespace HelfgottQuadratic

noncomputable def primePlusProduct (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, ((p:ℝ)+1)

theorem primePlusProduct_pos (n : ℕ) : 0 < primePlusProduct n := by
  exact prod_pos (fun p hp => by positivity)

theorem squarefree_le_primePlusProduct (n : ℕ) (hn : Squarefree n) :
    (n:ℝ) ≤ primePlusProduct n := by
  calc
    (n:ℝ) = ∏ p ∈ n.primeFactors, (p:ℝ) := by
      rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hn]
    _ ≤ primePlusProduct n :=
      prod_le_prod (fun p hp => Nat.cast_nonneg p) (fun p hp => by linarith)

theorem mobius_sigma_convolution_weight (n : ℕ) (hn : 1 ≤ n) :
    ((moebius n:ℤ):ℝ)^2/((n:ℝ)*primePlusProduct n) ≤ 1/(n:ℝ)^2 := by
  by_cases hs : Squarefree n
  · have hm : ((moebius n:ℤ):ℝ)^2=1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hs
    rw [hm]
    apply one_div_le_one_div_of_le (by positivity)
    have hh := squarefree_le_primePlusProduct n hs
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  · rw [moebius_eq_zero_of_not_squarefree hs]
    simp only [Int.cast_zero,zero_pow (by decide : 2≠0),zero_div]
    positivity

theorem mobius_sigma_square_weight (n : ℕ) (hn : 1 ≤ n) :
    |((moebius n:ℤ):ℝ)|/(primePlusProduct n)^2 ≤ 1/(n:ℝ)^2 := by
  by_cases hs : Squarefree n
  · have hm : |((moebius n:ℤ):ℝ)|=1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hs
    rw [hm]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (squarefree_le_primePlusProduct n hs) 2
  · rw [moebius_eq_zero_of_not_squarefree hs]
    simp only [Int.cast_zero,abs_zero,zero_div]
    positivity

theorem reciprocal_square_finite_bound (N : ℕ) :
    (∑ n ∈ Icc 1 N, 1/(n:ℝ)^2) ≤ Real.pi^2/6 := by
  rw [← hasSum_zeta_two.tsum_eq]
  exact hasSum_zeta_two.summable.sum_le_tsum (Icc 1 N) (fun n hn => by positivity)

theorem coprime_mobius_sigma_abs_bound (q N : ℕ) :
    |∑ n ∈ Icc 1 N, if Nat.Coprime n q then
      ((moebius n:ℤ):ℝ)/primePlusProduct n else 0| ≤ Real.pi^2/6 := by
  change |∑ n ∈ Icc 1 N, if Nat.Coprime n q then
      ((moebius n:ℤ):ℝ)/(∏ p ∈ n.primeFactors, ((p:ℝ)+1)) else 0| ≤ _
  rw [HelfgottSigma.mobius_sigma_coprime_partial_sum_convolution_complete]
  apply ((abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun n hn => ?_))).trans
    (reciprocal_square_finite_bound N)
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc,abs_mul,abs_of_nonneg (by positivity :
      0 ≤ ((moebius n:ℤ):ℝ)^2/((n:ℝ)*(∏ p ∈ n.primeFactors, ((p:ℝ)+1))))]
    apply (mul_le_mul_of_nonneg_left (coprime_mobius_reciprocal_abs_le_one (n*q) (N/n))
      (by positivity)).trans
    simpa only [mul_one,primePlusProduct] using mobius_sigma_convolution_weight n (mem_Icc.mp hn).1
  · rw [if_neg hc,abs_zero]
    positivity

end HelfgottQuadratic

end

section

open Finset ArithmeticFunction
open scoped BigOperators
namespace HelfgottQuadratic

theorem coprime_prime_attenuation_bound (s : Finset ℕ) (N : ℕ) (f t : ℕ → ℝ)
    (hprime : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ s, 0≤t p ∧ t p≤1)
    (hbase : ∀ q : ℕ, |∑ n ∈ Icc 1 N, if Nat.Coprime n q then f n else 0|≤1)
    (q : ℕ) :
    |∑ n ∈ Icc 1 N, if Nat.Coprime n q then
      f n*(∏ p ∈ s, if p∣n then t p else 1) else 0|≤1 := by
  induction s using Finset.induction_on generalizing q with
  | empty => simpa using hbase q
  | @insert p s hps ih =>
    have hp := hprime p (mem_insert_self _ _)
    have htp := ht p (mem_insert_self _ _)
    have hpr : ∀ r ∈ s, r.Prime := fun r hr => hprime r (mem_insert_of_mem hr)
    have htr : ∀ r ∈ s, 0≤t r ∧ t r≤1 := fun r hr => ht r (mem_insert_of_mem hr)
    let A := fun q : ℕ => ∑ n ∈ Icc 1 N, if Nat.Coprime n q then
      f n*(∏ r ∈ s, if r∣n then t r else 1) else 0
    have hA : |A q|≤1 := ih hpr htr q
    have hB : |A (q*p)|≤1 := ih hpr htr (q*p)
    have he : (∑ n ∈ Icc 1 N, if Nat.Coprime n q then
        f n*(∏ r ∈ insert p s, if r∣n then t r else 1) else 0) =
        t p*A q+(1-t p)*A (q*p) := by
      dsimp only [A]
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro n hn
      rw [prod_insert hps]
      simp only [Nat.coprime_mul_iff_right]
      have hcp : Nat.Coprime n p ↔ ¬p∣n := by rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd
      simp only [hcp]
      by_cases hq : Nat.Coprime n q <;> by_cases hpn : p∣n <;>
        simp only [hq,hpn,ite_true,ite_false,true_and,and_true,false_and,and_false,
          not_true_eq_false,not_false_eq_true,mul_one,zero_mul,mul_zero] <;> (try split_ifs) <;> ring
    rw [he]
    calc
      _ ≤ |t p*A q|+|(1-t p)*A (q*p)| := abs_add_le _ _
      _ = t p*|A q|+(1-t p)*|A (q*p)| := by
        rw [abs_mul,abs_mul,abs_of_nonneg htp.1,abs_of_nonneg (sub_nonneg.mpr htp.2)]
      _ ≤ t p*1+(1-t p)*1 := add_le_add
        (mul_le_mul_of_nonneg_left hA htp.1)
        (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr htp.2))
      _ = 1 := by ring

theorem prime_attenuation_sigma_identity (N n : ℕ) (hn : 1≤n) (hnN : n≤N) :
    (((moebius n:ℤ):ℝ)/(n:ℝ))*(∏ p ∈ (Icc 1 N).filter Nat.Prime,
      if p∣n then (p:ℝ)/((p:ℝ)+1) else 1) =
      ((moebius n:ℤ):ℝ)/primePlusProduct n := by
  by_cases hs : Squarefree n
  · have hn0 : n≠0 := by omega
    have hsub : n.primeFactors ⊆ (Icc 1 N).filter Nat.Prime := by
      intro p hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_primeFactors hp,
        (Nat.le_of_mem_primeFactors hp).trans hnN⟩,Nat.prime_of_mem_primeFactors hp⟩
    have he : (∏ p ∈ (Icc 1 N).filter Nat.Prime, if p∣n then (p:ℝ)/((p:ℝ)+1) else 1) =
        ∏ p ∈ n.primeFactors, (p:ℝ)/((p:ℝ)+1) := by
      calc
        _ = ∏ p ∈ n.primeFactors, if p∣n then (p:ℝ)/((p:ℝ)+1) else 1 := by
          symm
          apply prod_subset hsub
          intro p hp hpnot
          rw [if_neg (fun hpn => hpnot ((mem_filter.mp hp).2.mem_primeFactors hpn hn0))]
        _ = _ := prod_congr rfl (fun p hp => if_pos (Nat.dvd_of_mem_primeFactors hp))
    rw [he,prod_div_distrib,← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hs]
    change _ = ((moebius n:ℤ):ℝ)/primePlusProduct n
    have hnr : (n:ℝ)≠0 := by exact_mod_cast hn0
    change _ = ((moebius n:ℤ):ℝ)/(∏ p ∈ n.primeFactors, ((p:ℝ)+1))
    field_simp
  · rw [moebius_eq_zero_of_not_squarefree hs]
    simp

theorem coprime_mobius_sigma_abs_le_one (q N : ℕ) :
    |∑ n ∈ Icc 1 N, if Nat.Coprime n q then
      ((moebius n:ℤ):ℝ)/primePlusProduct n else 0|≤1 := by
  have hh := coprime_prime_attenuation_bound ((Icc 1 N).filter Nat.Prime) N
    (fun n => ((moebius n:ℤ):ℝ)/(n:ℝ)) (fun p => (p:ℝ)/((p:ℝ)+1))
    (fun p hp => (mem_filter.mp hp).2)
    (by intro p hp; constructor; positivity; exact div_le_one_of_le₀ (by linarith) (by positivity))
    (fun q => coprime_mobius_reciprocal_abs_le_one q N) q
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro n hn
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc,if_pos hc,prime_attenuation_sigma_identity N n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2]
  · rw [if_neg hc,if_neg hc]

end HelfgottQuadratic

end

open Finset ArithmeticFunction
open scoped BigOperators

theorem solution (q N : ℕ) :
    |∑ n ∈ Icc 1 N, if Nat.Coprime n q then
      ((moebius n:ℤ):ℝ)/(∏ p ∈ n.primeFactors, ((p:ℝ)+1)) else 0|≤1 := by
  exact HelfgottQuadratic.coprime_mobius_sigma_abs_le_one q N
