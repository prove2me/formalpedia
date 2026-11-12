-- Prove2me | solution 1 for Helfgott.vaughan_mobius_complementary_energy
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T21:11:49.555206+00:00
-- url     : https://prove2.me/submissions/c6a54c7a-53e8-49c1-82ca-11eb5ce7b252

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_Helfgott_VaughanData
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Algebra.Order.Floor.Semiring
import Theorems.Thm_Helfgott_actual_vaughan_mobius_interval_density_uniform_error
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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
/- Retained accepted Prove2Me proof 180f8108-2b6f-4d9d-b1c1-a7e7f1e8342c by raresbuhai, Apache 2.0. -/
section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def vaughan_two_power_compact_strictMobiusCutoffLength (Y : ℕ) (U z : ℝ) : ℕ :=
  min Y (⌈z/U⌉₊-1)

lemma vaughan_two_power_compact_strict_mobius_cutoff_divisor_iff (Y d a : ℕ) (U z : ℝ)
    (hd : 1 ≤ d) (ha : 1 ≤ a) (hU : 0 < U) :
    (a ≤ Y/d ∧ U*(d*a : ℕ)<z) ↔ a ≤ vaughan_two_power_compact_strictMobiusCutoffLength Y U z/d := by
  have hceil : d*a<⌈z/U⌉₊ ↔ U*(d*a : ℕ)<z := by
    rw [Nat.lt_ceil, lt_div_iff₀ hU]
    rw [mul_comm]
  have hcut : U*(d*a : ℕ)<z ↔ d*a ≤ ⌈z/U⌉₊-1 := by
    have hda : 1 ≤ d*a := Nat.mul_le_mul hd ha
    rw [← hceil]
    omega
  rw [hcut, Nat.le_div_iff_mul_le (by omega), Nat.le_div_iff_mul_le (by omega)]
  unfold vaughan_two_power_compact_strictMobiusCutoffLength
  rw [le_min_iff]
  simp only [Nat.mul_comm]

lemma vaughan_two_power_compact_strict_mobius_cutoff_partial_sum_eq (f : ℕ → ℝ) (q Y d : ℕ) (U z : ℝ)
    (hd : 1 ≤ d) (hU : 0 < U) :
    (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0) =
      ∑ a∈Icc 1 (vaughan_two_power_compact_strictMobiusCutoffLength Y U z/d), if Nat.Coprime a (d*q) then f a else 0 := by
  have hfilter : (Icc 1 (Y/d)).filter (fun a => U*(d*a : ℕ)<z) =
      Icc 1 (vaughan_two_power_compact_strictMobiusCutoffLength Y U z/d) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      exact ⟨h.1.1,(vaughan_two_power_compact_strict_mobius_cutoff_divisor_iff Y d a U z hd h.1.1 hU).mp ⟨h.1.2,h.2⟩⟩
    · intro h
      have hi := (vaughan_two_power_compact_strict_mobius_cutoff_divisor_iff Y d a U z hd h.1 hU).mpr h.2
      exact ⟨⟨h.1,hi.1⟩,hi.2⟩
  calc
    _ = ∑ a∈Icc 1 (Y/d), if U*(d*a : ℕ)<z then
        (if Nat.Coprime a (d*q) then f a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hc : Nat.Coprime a (d*q) <;> by_cases ht : U*(d*a : ℕ)<z <;>
        simp only [hc,ht,and_true,and_false,true_and,false_and,ite_true,ite_false]
    _ = ∑ a∈(Icc 1 (Y/d)).filter (fun a => U*(d*a : ℕ)<z),
        if Nat.Coprime a (d*q) then f a else 0 := (Finset.sum_filter _ _).symm
    _ = _ := by rw [hfilter]

theorem vaughan_two_power_compact_mobius_sigma_coprime_strict_cutoff_energy_eq (q Y : ℕ) (U z : ℝ) (hU : 0 < U) :
    let X : ℕ := min Y (⌈z/U⌉₊-1)
    let sigma : ℕ → ℝ := fun n => ∏ p∈n.primeFactors, ((p : ℝ)+1)
    (∑ d∈Icc 1 Y, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then
        ((moebius a : ℤ) : ℝ)/sigma a else 0)^2 else 0) =
    (∑ d∈Icc 1 X, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (X/d), if Nat.Coprime a (d*q) then
        ((moebius a : ℤ) : ℝ)/sigma a else 0)^2 else 0) := by
  let X := vaughan_two_power_compact_strictMobiusCutoffLength Y U z
  let sigma : ℕ → ℝ := fun n => ∏ p∈n.primeFactors, ((p : ℝ)+1)
  let f : ℕ → ℝ := fun a => ((moebius a : ℤ) : ℝ)/sigma a
  let g : ℕ → ℝ := fun d => if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
    (∑ a∈Icc 1 (X/d), if Nat.Coprime a (d*q) then f a else 0)^2 else 0
  change (∑ d∈Icc 1 Y, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0)^2 else 0) =
    ∑ d∈Icc 1 X, g d
  have hinner : (∑ d∈Icc 1 Y, if Nat.Coprime d q then |((moebius d : ℤ) : ℝ)|/(sigma d)^2 *
      (∑ a∈Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0)^2 else 0) =
    ∑ d∈Icc 1 Y, g d := by
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [g]
    rw [vaughan_two_power_compact_strict_mobius_cutoff_partial_sum_eq f q Y d U z (Finset.mem_Icc.mp hd).1 hU]
  rw [hinner]
  have hXY : X ≤ Y := min_le_left _ _
  have hsub : Icc 1 X ⊆ Icc 1 Y := fun d hd =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hXY⟩
  exact (Finset.sum_subset hsub (fun d hdY hdX => by
    have hd : 1 ≤ d := (Finset.mem_Icc.mp hdY).1
    have hXd : X < d := by
      have hn : ¬d≤X := fun h => hdX (Finset.mem_Icc.mpr ⟨hd,h⟩)
      omega
    have hdiv : X/d = 0 := Nat.div_eq_of_lt hXd
    simp [g,hdiv])).symm

end Helfgott
end


end

section
section
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott
lemma moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h


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


theorem finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r :=
  HelfgottQuadratic.finite_positive_divisor_reindex B F
end Helfgott
end

end

section
/- Retained accepted Prove2Me proof 50bdc832-4cc8-484c-af03-e67ce464565f by raresbuhai, Apache 2.0.
General density normalization and cutoff integral lemmas; odd-only specializations omitted. -/
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma prime_ratio_product_mul (m n : ℕ) (hc : Nat.Coprime m n) :
    (∏ p∈(m*n).primeFactors,(p : ℝ)/((p : ℝ)+1))=
      (∏ p∈m.primeFactors,(p : ℝ)/((p : ℝ)+1))*
      (∏ p∈n.primeFactors,(p : ℝ)/((p : ℝ)+1)) := by
  rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]

lemma signed_mobius_prime_ratio_normalization (n : ℕ) :
    ((moebius n : ℤ) : ℝ)*(∏ p∈n.primeFactors,(p : ℝ)/((p : ℝ)+1))=
      ((moebius n : ℤ) : ℝ)*(n : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1)) := by
  by_cases hn : Squarefree n
  · rw [Finset.prod_div_distrib,←Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hn]
    ring
  · rw [moebius_eq_zero_of_not_squarefree hn]
    simp

lemma signed_mobius_pair_density_normalization (r t v : ℕ)
    (hrt : Nat.Coprime r t) (hrtv : Nat.Coprime (r*t) v) :
    ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
      ((6/Real.pi^2)*(∏ p∈(r*t*v).primeFactors,(p : ℝ)/((p : ℝ)+1)))=
      ((6/Real.pi^2)*(∏ p∈v.primeFactors,(p : ℝ)/((p : ℝ)+1)))*
      (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
      (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1)))*(r : ℝ)*(t : ℝ) := by
  rw [prime_ratio_product_mul (r*t) v hrtv,prime_ratio_product_mul r t hrt]
  have hr := signed_mobius_prime_ratio_normalization r
  have ht := signed_mobius_prime_ratio_normalization t
  calc
    _=(6/Real.pi^2)*(∏ p∈v.primeFactors,(p : ℝ)/((p : ℝ)+1))*
      (((moebius r : ℤ) : ℝ)*(∏ p∈r.primeFactors,(p : ℝ)/((p : ℝ)+1)))*
      (((moebius t : ℤ) : ℝ)*(∏ p∈t.primeFactors,(p : ℝ)/((p : ℝ)+1))) := by ring
    _=_ := by rw [hr,ht];ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma density_cutoff_product_normalization (U A B r t s : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hs : 1 ≤ s) :
    (r : ℝ)*(t : ℝ)*((B : ℝ)/(r*t*s : ℕ)-
      max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t)))=
      (B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r)) := by
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hr
  have ht0 : (t : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt ht
  have hs0 : (s : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hs
  have hp : 0 ≤ (r : ℝ)*(t : ℝ) := by positivity
  rw [mul_assoc,←mul_assoc,mul_sub,mul_max_of_nonneg _ _ hp,mul_max_of_nonneg _ _ hp]
  have hB : (r : ℝ)*(t : ℝ)*((B : ℝ)/(r*t*s : ℕ))=(B : ℝ)/(s : ℝ) := by
    push_cast;field_simp <;> ring
  have hA : (r : ℝ)*(t : ℝ)*((A : ℝ)/(r*t*s : ℕ))=(A : ℝ)/(s : ℝ) := by
    push_cast;field_simp <;> ring
  have hUr : (r : ℝ)*(t : ℝ)*((U : ℝ)/r)=(U : ℝ)*t := by field_simp <;> ring
  have hUt : (r : ℝ)*(t : ℝ)*((U : ℝ)/t)=(U : ℝ)*r := by field_simp <;> ring
  rw [hB,hA,hUr,hUt]

lemma signed_mobius_interval_density_normalization (U A B r t s v : ℕ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) (hs : 1 ≤ s)
    (hrt : Nat.Coprime r t) (hrtv : Nat.Coprime (r*t) v) :
    ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
      (((B : ℝ)/(r*t*s : ℕ)-max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t)))*
        ((6/Real.pi^2)*(∏ p∈(r*t*v).primeFactors,(p : ℝ)/((p : ℝ)+1))))=
      ((6/Real.pi^2)*(∏ p∈v.primeFactors,(p : ℝ)/((p : ℝ)+1)))*
      (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
      (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1)))*
      ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) := by
  have hd := signed_mobius_pair_density_normalization r t v hrt hrtv
  calc
    _=(((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
      ((6/Real.pi^2)*(∏ p∈(r*t*v).primeFactors,(p : ℝ)/((p : ℝ)+1))))*
      ((B : ℝ)/(r*t*s : ℕ)-max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))) := by ring
    _=_ := by
      rw [hd]
      linear_combination
        ((6/Real.pi^2)*(∏ p∈v.primeFactors,(p : ℝ)/((p : ℝ)+1)))*
        (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
        (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1)))*
        (density_cutoff_product_normalization U A B r t s hr ht hs)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma actual_vaughan_signed_density_main_normalization (U A B v : ℕ) :
    let rho : ℕ→ℝ := fun q => (6/Real.pi^2)*∏ p∈q.primeFactors,(p : ℝ)/((p : ℝ)+1)
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    let L : ℕ→ℕ→ℕ→ℝ := fun s r t => max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))
    (∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
      if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
        ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
          (((B : ℝ)/(r*t*s : ℕ)-L s r t)*rho (r*t*v)) else 0)=
      rho v*(∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
          (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t)*
            ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) else 0) := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v
  · rw [if_pos hc,if_pos hc]
    simpa only [mul_assoc] using signed_mobius_interval_density_normalization U A B r t s v
      (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp hs).1 hc.1
      (hc.2.of_dvd_left (dvd_mul_right (r*t) s))
  · rw [if_neg hc,if_neg hc,mul_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma cutoff_indicator_interval_integrable (c a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => if c<x then (1:ℝ) else 0) volume a b := by
  have hm : Measurable (fun x : ℝ => if c<x then (1:ℝ) else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  apply (intervalIntegrable_const (c:=(1:ℝ))).mono_fun' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by dsimp only;split_ifs <;> norm_num)

lemma cutoff_indicator_interval_integral (a b c : ℝ) (hab : a ≤ b) (hcb : c ≤ b) :
    (∫ x in a..b,if c<x then (1:ℝ) else 0)=b-max a c := by
  by_cases hca : c ≤ a
  · rw [max_eq_left hca]
    have he : (∫ x in a..b,if c<x then (1:ℝ) else 0)=∫ x in a..b,(1:ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro x hx
      exact if_pos (hca.trans_lt hx.1)
    rw [he,intervalIntegral.integral_const]
    simp
  · have hac : a ≤ c := le_of_not_ge hca
    rw [max_eq_right hac]
    have hleft : (∫ x in a..c,if c<x then (1:ℝ) else 0)=0 := by
      calc
        _=∫ x in a..c,(0:ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hac
          intro x hx
          exact if_neg (by linarith [hx.2])
        _=0 := by simp
    have hright : (∫ x in c..b,if c<x then (1:ℝ) else 0)=b-c := by
      calc
        _=∫ x in c..b,(1:ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hcb
          intro x hx
          exact if_pos hx.1
        _=b-c := by simp
    have h := intervalIntegral.integral_add_adjacent_intervals
      (cutoff_indicator_interval_integrable c a c) (cutoff_indicator_interval_integrable c c b)
    rw [hleft,hright,zero_add] at h
    exact h.symm

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

theorem signed_finite_cutoff_sum_integral (S : Finset ℕ) (T : Finset ℕ)
    (w : ℕ→ℕ→ℝ) (c : ℕ→ℕ→ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ r∈S,∀ t∈T,c r t ≤ b) :
    (∑ r∈S,∑ t∈T,w r t*(b-max a (c r t)))=
      ∫ x in a..b,∑ r∈S,∑ t∈T,if c r t<x then w r t else 0 := by
  have hi (r t : ℕ) : IntervalIntegrable (fun x : ℝ => if c r t<x then w r t else 0) volume a b := by
    have h := (cutoff_indicator_interval_integrable (c r t) a b).const_mul (w r t)
    apply h.congr
    intro x hx
    dsimp only
    split_ifs <;> simp
  have hs (r : ℕ) : IntervalIntegrable (fun x : ℝ => ∑ t∈T,if c r t<x then w r t else 0) volume a b :=
    by
      have he : (∑ t∈T,fun x : ℝ => if c r t<x then w r t else 0)=
          (fun x : ℝ => ∑ t∈T,if c r t<x then w r t else 0) := by
        funext x
        simp
      rw [←he]
      exact IntervalIntegrable.sum T (fun t ht => hi r t)
  rw [intervalIntegral.integral_finsetSum (fun r hr => hs r)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [intervalIntegral.integral_finsetSum (fun t ht => hi r t)]
  apply Finset.sum_congr rfl
  intro t ht
  have he : (fun x : ℝ => if c r t<x then w r t else 0)=
      (fun x : ℝ => w r t*(if c r t<x then (1:ℝ) else 0)) := by
    funext x
    split_ifs <;> simp
  rw [he,intervalIntegral.integral_const_mul,cutoff_indicator_interval_integral a b (c r t) hab (hc r hr t ht)]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

lemma vaughan_density_integral_cutoffs (U B r t s : ℕ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) (hs : 1 ≤ s)
    (hrcap : r ≤ B/((U+1)*s)) (htcap : t ≤ B/((U+1)*s)) :
    max ((U : ℝ)*t) ((U : ℝ)*r) ≤ (B : ℝ)/(s : ℝ) := by
  have hd : 0<(U+1)*s := Nat.mul_pos (Nat.succ_pos U) hs
  have hrP := (Nat.le_div_iff_mul_le hd).mp hrcap
  have htP := (Nat.le_div_iff_mul_le hd).mp htcap
  have hrB : U*r*s ≤ B := by
    calc
      _ ≤ (U+1)*r*s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ U))
      _=r*((U+1)*s) := by ring
      _ ≤ B := hrP
  have htB : U*t*s ≤ B := by
    calc
      _ ≤ (U+1)*t*s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ U))
      _=t*((U+1)*s) := by ring
      _ ≤ B := htP
  have hsR : (0:ℝ)<s := by exact_mod_cast hs
  apply max_le
  · exact (le_div_iff₀ hsR).mpr (by exact_mod_cast htB)
  · exact (le_div_iff₀ hsR).mpr (by exact_mod_cast hrB)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma actual_vaughan_signed_density_main_integral (U A B v : ℕ) (hAB : A ≤ B) :
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    (∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
      if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
        (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t)*
          ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) else 0)=
      ∑ s∈Finset.Icc 1 (B/(U+1)),∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),
        ∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
          if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v ∧ (U : ℝ)*r<z ∧ (U : ℝ)*t<z then
            (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t) else 0 := by
  dsimp only
  apply Finset.sum_congr rfl
  intro s hs
  let T := Finset.Icc 1 (B/((U+1)*s))
  let w : ℕ→ℕ→ℝ := fun r t => if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
    (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
    (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1))) else 0
  have hi := signed_finite_cutoff_sum_integral T T w
    (fun r t => max ((U : ℝ)*t) ((U : ℝ)*r)) ((A : ℝ)/(s : ℝ)) ((B : ℝ)/(s : ℝ))
    (div_le_div_of_nonneg_right (by exact_mod_cast hAB) (by positivity))
    (fun r hr t ht => vaughan_density_integral_cutoffs U B r t s (Finset.mem_Icc.mp hr).1
      (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hr).2 (Finset.mem_Icc.mp ht).2)
  have hleft : (∑ r∈T,∑ t∈T,w r t*((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))))=
      ∑ r∈T,∑ t∈T,if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
        (((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors,((p : ℝ)+1)))*
        (((moebius t : ℤ) : ℝ)/(∏ p∈t.primeFactors,((p : ℝ)+1)))*
        ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [w]
    split_ifs <;> simp
  rw [hleft] at hi
  rw [hi]
  apply intervalIntegral.integral_congr
  intro z hz
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  dsimp [w]
  split_ifs <;> simp_all only [max_lt_iff] <;> aesop

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

lemma mobius_sigma_weighted_pair_common_divisor (d a b q : ℕ) (h : ℕ→ℝ) :
    ((moebius d : ℤ) : ℝ)*
      (if Nat.Coprime (d*a) q ∧ Nat.Coprime (d*b) q then
        (mobiusSigmaWeight (d*a)*h (d*a))*(mobiusSigmaWeight (d*b)*h (d*b)) else 0)=
      if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then mobiusSigmaWeight a*h (d*a) else 0)*
          (if Nat.Coprime b (d*q) then mobiusSigmaWeight b*h (d*b) else 0) else 0 := by
  have hp := mobius_sigma_pair_common_divisor d a b q
  have he := congrArg (fun x : ℝ => x*h (d*a)*h (d*b)) hp
  convert he using 1 <;> split_ifs <;> ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_sigma_weighted_coprime_pair_square_decomposition (q Y : ℕ) (h : ℕ→ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (f r*h r)*(f t*h t) else 0)=
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a*h (d*a) else 0)^2 else 0 := by
  change (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0)=_
  have hleft : (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0)=
      ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,if Nat.Coprime r t then
        (if Nat.Coprime r q ∧ Nat.Coprime t q then (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0) else 0 := by
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
        (mobiusSigmaWeight (d*a)*h (d*a))*(mobiusSigmaWeight (d*b)*h (d*b)) else 0))=
      ∑ a∈Finset.Icc 1 (Y/d),∑ b∈Finset.Icc 1 (Y/d),
        if Nat.Coprime d q then (((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (if Nat.Coprime a (d*q) then mobiusSigmaWeight a*h (d*a) else 0)*
          (if Nat.Coprime b (d*q) then mobiusSigmaWeight b*h (d*b) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    exact Finset.sum_congr rfl (fun b hb => mobius_sigma_weighted_pair_common_divisor d a b q h)
  rw [he]
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc]
    simp only [if_pos hc]
    simp_rw [←Finset.mul_sum]
    rw [←Finset.sum_mul,←Finset.mul_sum]
    change _=(((moebius d : ℤ) : ℝ)/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
      (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then mobiusSigmaWeight a*h (d*a) else 0)^2
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

theorem mobius_sigma_weighted_coprime_pair_quadratic_bound (q Y : ℕ) (h : ℕ→ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then (f r*h r)*(f t*h t) else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then f a*h (d*a) else 0)^2 else 0 := by
  dsimp only
  rw [mobius_sigma_weighted_coprime_pair_square_decomposition]
  apply (abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc,if_pos hc,abs_mul,abs_div,
      abs_of_nonneg (sq_nonneg (∏ p∈d.primeFactors,((p : ℝ)+1))),abs_of_nonneg (sq_nonneg (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then (((moebius a : ℤ) : ℝ)/(∏ p∈a.primeFactors,((p : ℝ)+1)))*h (d*a) else 0))]
  · rw [if_neg hc,if_neg hc,abs_zero]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem mobius_sigma_cutoff_coprime_pair_quadratic_bound (q Y : ℕ) (U z : ℝ) :
    let f : ℕ→ℝ := fun n => ((moebius n : ℤ) : ℝ)/(∏ p∈n.primeFactors,((p : ℝ)+1))
    |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then f r*f t else 0| ≤
      ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then f a else 0)^2 else 0 := by
  let h : ℕ→ℝ := fun n => if U*n<z then 1 else 0
  have hb := mobius_sigma_weighted_coprime_pair_quadratic_bound q Y h
  dsimp only at hb ⊢
  have hleft : (∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
      if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
        (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0)=
      ∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
        if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then
          mobiusSigmaWeight r*mobiusSigmaWeight t else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [h]
    split_ifs <;> simp_all <;> try linarith <;> aesop
  have hright (d : ℕ) : (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) then
        mobiusSigmaWeight a*h (d*a) else 0)=
      ∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then mobiusSigmaWeight a else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [h]
    split_ifs <;> simp_all <;> try linarith <;> aesop
  change |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
    if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q then
      (mobiusSigmaWeight r*h r)*(mobiusSigmaWeight t*h t) else 0|≤_ at hb
  rw [hleft] at hb
  change |∑ r∈Finset.Icc 1 Y,∑ t∈Finset.Icc 1 Y,
    if Nat.Coprime r t ∧ Nat.Coprime r q ∧ Nat.Coprime t q ∧ U*r<z ∧ U*t<z then
      mobiusSigmaWeight r*mobiusSigmaWeight t else 0|≤_
  exact hb.trans_eq (Finset.sum_congr rfl (fun d hd => by
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,if_pos hc]
      congr 1
      exact congrArg (fun x : ℝ => x^2) (hright d)
    · rw [if_neg hc,if_neg hc]))

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma finite_coprime_cutoff_sum_measurable (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) :
    Measurable (fun z : ℝ => ∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0) := by
  apply Finset.measurable_sum
  intro a ha
  by_cases hc : Nat.Coprime a q
  · have he : (fun z : ℝ => if Nat.Coprime a q ∧ c a<z then w a else 0)=
        (fun z : ℝ => if c a<z then w a else 0) := by
      funext z
      by_cases hz : c a<z
      · rw [if_pos ⟨hc,hz⟩,if_pos hz]
      · rw [if_neg (show ¬(Nat.Coprime a q ∧ c a<z) from by aesop),if_neg hz]
    rw [he]
    exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
  · have he : (fun z : ℝ => if Nat.Coprime a q ∧ c a<z then w a else 0)=(fun _ : ℝ => (0:ℝ)) := by
      funext z;simp only [hc,false_and,if_false]
    rw [he]
    exact measurable_const

lemma finite_coprime_cutoff_sum_abs_bound (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) (z : ℝ) :
    |∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0|≤∑ a∈S,|w a| := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  split_ifs
  · exact le_rfl
  · simp only [abs_zero]
    exact abs_nonneg _

lemma finite_coprime_cutoff_square_interval_integrable (S : Finset ℕ) (q : ℕ) (w c : ℕ→ℝ) (l r : ℝ) :
    IntervalIntegrable (fun z : ℝ => (∑ a∈S,if Nat.Coprime a q ∧ c a<z then w a else 0)^2) volume l r := by
  have hm := (finite_coprime_cutoff_sum_measurable S q w c).pow_const 2
  apply (intervalIntegrable_const (c:=(∑ a∈S,|w a|)^2)).mono_fun' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := finite_coprime_cutoff_sum_abs_bound S q w c z
  have hs : 0≤∑ a∈S,|w a| := Finset.sum_nonneg (fun a ha => abs_nonneg _)
  exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hs] using hb)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma finite_interval_integrable_sum {ι : Type} (S : Finset ι) (f : ι→ℝ→ℝ) (l r : ℝ)
    (hf : ∀ i∈S,IntervalIntegrable (f i) volume l r) :
    IntervalIntegrable (fun z => ∑ i∈S,f i z) volume l r := by
  have he : (∑ i∈S,f i)=(fun z => ∑ i∈S,f i z) := by funext z;simp
  rw [←he]
  exact IntervalIntegrable.sum S hf

lemma finite_filtered_cutoff_pair_interval_integrable (S T : Finset ℕ)
    (P : ℕ→ℕ→Prop) [∀ a b,Decidable (P a b)] (w c : ℕ→ℕ→ℝ) (l r : ℝ) :
    IntervalIntegrable (fun z => ∑ a∈S,∑ b∈T,if P a b ∧ c a b<z then w a b else 0) volume l r := by
  apply finite_interval_integrable_sum
  intro a ha
  apply finite_interval_integrable_sum
  intro b hb
  by_cases hP : P a b
  · have hi := (cutoff_indicator_interval_integrable (c a b) l r).const_mul (w a b)
    apply hi.congr
    intro z hz
    dsimp only
    by_cases hc : c a b<z
    · rw [if_pos hc,if_pos ⟨hP,hc⟩,mul_one]
    · rw [if_neg hc,if_neg (show ¬(P a b ∧ c a b<z) from by aesop),mul_zero]
  · have he : (fun z : ℝ => if P a b ∧ c a b<z then w a b else 0)=(fun _ => (0:ℝ)) := by
      funext z
      exact if_neg (by aesop)
    rw [he]
    exact intervalIntegrable_const

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
namespace Helfgott

lemma mobius_sigma_cutoff_pair_interval_integrable (q Y : ℕ) (U l r : ℝ) :
    IntervalIntegrable (fun z => ∑ a∈Finset.Icc 1 Y,∑ b∈Finset.Icc 1 Y,
      if Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q ∧ U*a<z ∧ U*b<z then
        mobiusSigmaWeight a*mobiusSigmaWeight b else 0) volume l r := by
  have hi := finite_filtered_cutoff_pair_interval_integrable (Finset.Icc 1 Y) (Finset.Icc 1 Y)
    (fun a b => Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q)
    (fun a b => mobiusSigmaWeight a*mobiusSigmaWeight b) (fun a b => max (U*a) (U*b)) l r
  apply hi.congr
  intro z hz
  dsimp only
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp_all only [max_lt_iff] <;> aesop

lemma mobius_sigma_cutoff_quadratic_interval_integrable (q Y : ℕ) (U l r : ℝ) :
    IntervalIntegrable (fun z => ∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
      (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
        (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then mobiusSigmaWeight a else 0)^2 else 0) volume l r := by
  apply finite_interval_integrable_sum
  intro d hd
  by_cases hc : Nat.Coprime d q
  · have hi := (finite_coprime_cutoff_square_interval_integrable (Finset.Icc 1 (Y/d)) (d*q)
        mobiusSigmaWeight (fun a => U*(d*a : ℕ)) l r).const_mul
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)
    simpa only [if_pos hc] using hi
  · simpa only [if_neg hc] using (intervalIntegrable_const (c:=(0:ℝ)) : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume l r)

theorem mobius_sigma_cutoff_integral_quadratic_upper (q Y : ℕ) (U l r : ℝ) (hlr : l≤r) :
    (∫ z in l..r,∑ a∈Finset.Icc 1 Y,∑ b∈Finset.Icc 1 Y,
      if Nat.Coprime a b ∧ Nat.Coprime a q ∧ Nat.Coprime b q ∧ U*a<z ∧ U*b<z then
        mobiusSigmaWeight a*mobiusSigmaWeight b else 0)≤
      ∫ z in l..r,∑ d∈Finset.Icc 1 Y,if Nat.Coprime d q then
        (|((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2)*
          (∑ a∈Finset.Icc 1 (Y/d),if Nat.Coprime a (d*q) ∧ U*(d*a : ℕ)<z then mobiusSigmaWeight a else 0)^2 else 0 := by
  apply intervalIntegral.integral_mono hlr
    (mobius_sigma_cutoff_pair_interval_integrable q Y U l r)
    (mobius_sigma_cutoff_quadratic_interval_integrable q Y U l r)
  intro z
  exact (le_abs_self _).trans (mobius_sigma_cutoff_coprime_pair_quadratic_bound q Y U z)

end Helfgott
end

end

section

open Finset ArithmeticFunction Helfgott MeasureTheory
open scoped BigOperators Interval
namespace HelfgottQuadratic

theorem mobius_sigma_cutoff_energy_uniform (q Y : ℕ) (U z : ℝ) (hU : 0 < U) :
    (∑ d ∈ Icc 1 Y, if Nat.Coprime d q then
      |((moebius d:ℤ):ℝ)|/(primePlusProduct d)^2 *
        (∑ a ∈ Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a:ℕ) < z then
          ((moebius a:ℤ):ℝ)/primePlusProduct a else 0)^2 else 0) ≤ (Real.pi^2/6)^3 := by
  change (∑ d ∈ Icc 1 Y, if Nat.Coprime d q then
      |((moebius d:ℤ):ℝ)|/(∏ p ∈ d.primeFactors, ((p:ℝ)+1))^2 *
        (∑ a ∈ Icc 1 (Y/d), if Nat.Coprime a (d*q) ∧ U*(d*a:ℕ) < z then
          ((moebius a:ℤ):ℝ)/(∏ p ∈ a.primeFactors, ((p:ℝ)+1)) else 0)^2 else 0) ≤ _
  rw [vaughan_two_power_compact_mobius_sigma_coprime_strict_cutoff_energy_eq q Y U z hU]
  dsimp only
  let X := min Y (⌈z/U⌉₊-1)
  have hp : 0 ≤ Real.pi^2/6 := by positivity
  calc
    _ ≤ ∑ d ∈ Icc 1 X, (1/(d:ℝ)^2)*(Real.pi^2/6)^2 := by
      apply sum_le_sum
      intro d hd
      by_cases hc : Nat.Coprime d q
      · rw [if_pos hc]
        have hm := coprime_mobius_sigma_abs_bound (d*q) (X/d)
        have hs := pow_le_pow_left₀ (abs_nonneg _) hm 2
        rw [sq_abs] at hs
        exact mul_le_mul (mobius_sigma_square_weight d (mem_Icc.mp hd).1) hs
          (sq_nonneg _) (by positivity)
      · rw [if_neg hc]
        positivity
    _ = (∑ d ∈ Icc 1 X, 1/(d:ℝ)^2)*(Real.pi^2/6)^2 := by rw [sum_mul]
    _ ≤ (Real.pi^2/6)*(Real.pi^2/6)^2 :=
      mul_le_mul_of_nonneg_right (reciprocal_square_finite_bound X) (sq_nonneg _)
    _ = _ := by ring

theorem mobius_sigma_cutoff_pair_integral_uniform (Y : ℕ) (U l r : ℝ)
    (hU : 0 < U) (hlr : l ≤ r) :
    (∫ z in l..r, ∑ a ∈ Icc 1 Y, ∑ b ∈ Icc 1 Y,
      if Nat.Coprime a b ∧ U*a < z ∧ U*b < z then
        mobiusSigmaWeight a*mobiusSigmaWeight b else 0) ≤
      (r-l)*(Real.pi^2/6)^3 := by
  have hb := mobius_sigma_cutoff_integral_quadratic_upper 1 Y U l r hlr
  simp only [Nat.coprime_one_right_iff,ite_true,true_and,and_true] at hb
  apply hb.trans
  have hh := intervalIntegral.integral_mono hlr
    (mobius_sigma_cutoff_quadratic_interval_integrable 1 Y U l r)
    (intervalIntegrable_const (c:=(Real.pi^2/6)^3))
    (fun z => mobius_sigma_cutoff_energy_uniform 1 Y U z hU)
  simpa only [Nat.coprime_one_right_iff,ite_true,intervalIntegral.integral_const,smul_eq_mul] using hh

end HelfgottQuadratic


end

section

open Finset ArithmeticFunction Helfgott MeasureTheory
open scoped BigOperators Interval
namespace HelfgottQuadratic

theorem vaughan_mobius_complementary_energy (U A B : ℕ)
    (hU : 1 ≤ U) (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    (∑ m ∈ Ioc A B,
      ((arithmeticTail U (moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) ≤
      (Real.pi^4/36)*((B:ℝ)-A)*(∑ s ∈ Icc 1 (B/(U+1)), 1/(s:ℝ))+
      (127/25:ℝ)*(∑' d:ℕ, 1/((d:ℝ)*Real.sqrt (d:ℝ)))^3*
        ((B:ℝ)*Real.sqrt (B:ℝ)/(U+1:ℕ)) := by
  have hb := actual_vaughan_mobius_interval_density_uniform_error U A B 1
    (by omega) hAB hhalf
  dsimp only at hb
  rw [actual_vaughan_signed_density_main_normalization,
    actual_vaughan_signed_density_main_integral U A B 1 hAB] at hb
  simp only [Nat.coprime_one_right_iff,ite_true,Nat.primeFactors_one,prod_empty,mul_one,
    true_and,and_true] at hb
  have hi : (∑ s ∈ Icc 1 (B/(U+1)),
      ∫ z in ((A:ℝ)/(s:ℝ))..((B:ℝ)/(s:ℝ)),
        ∑ r ∈ Icc 1 (B/((U+1)*s)), ∑ t ∈ Icc 1 (B/((U+1)*s)),
          if Nat.Coprime r t ∧ (U:ℝ)*r < z ∧ (U:ℝ)*t < z then
            mobiusSigmaWeight r*mobiusSigmaWeight t else 0) ≤
      ((B:ℝ)-A)*(Real.pi^2/6)^3*(∑ s ∈ Icc 1 (B/(U+1)), 1/(s:ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro s hs
    have hh := mobius_sigma_cutoff_pair_integral_uniform (B/((U+1)*s)) (U:ℝ)
      ((A:ℝ)/(s:ℝ)) ((B:ℝ)/(s:ℝ)) (by exact_mod_cast (show 0 < U by omega))
      (div_le_div_of_nonneg_right (by exact_mod_cast hAB) (Nat.cast_nonneg s))
    apply hh.trans_eq
    ring
  have hp := mul_le_mul_of_nonneg_left hi (show 0 ≤ 6/Real.pi^2 by positivity)
  have hupper := (le_abs_self _).trans hb
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have heq : (6/Real.pi^2)*(((B:ℝ)-A)*(Real.pi^2/6)^3*
      (∑ s ∈ Icc 1 (B/(U+1)), 1/(s:ℝ))) =
      (Real.pi^4/36)*((B:ℝ)-A)*(∑ s ∈ Icc 1 (B/(U+1)), 1/(s:ℝ)) := by
    field_simp
    <;> ring
  rw [heq] at hp
  change _ - (6/Real.pi^2)*_ ≤ _ at hupper
  dsimp only [mobiusSigmaWeight] at hp
  linarith

end HelfgottQuadratic


end

open Finset ArithmeticFunction Helfgott
open scoped BigOperators
theorem solution (U A B : ℕ)
    (hU : 1 ≤ U) (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    (∑ m ∈ Ioc A B,
      ((arithmeticTail U (moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) ≤
      (Real.pi^4/36)*((B:ℝ)-A)*(∑ s ∈ Icc 1 (B/(U+1)), 1/(s:ℝ))+
      (127/25:ℝ)*(∑' d:ℕ, 1/((d:ℝ)*Real.sqrt (d:ℝ)))^3*
        ((B:ℝ)*Real.sqrt (B:ℝ)/(U+1:ℕ)) := by
  exact HelfgottQuadratic.vaughan_mobius_complementary_energy U A B hU hAB hhalf
