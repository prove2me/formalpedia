-- Prove2me | solution 1 for Helfgott.squarefree_coprime_real_short_interval_euler_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T14:57:25.798171+00:00
-- url     : https://prove2.me/submissions/be3e606c-e5ce-466a-a27f-d26dda3ce314

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Floor.Semifield

section
set_option autoImplicit false
set_option maxHeartbeats 2300000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def reciprocalSquareArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n => 1/(n : ℝ)^2,by norm_num⟩

noncomputable def reciprocalFourthArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul reciprocalSquareArithmetic reciprocalSquareArithmetic

noncomputable def squarefreeReciprocalSquareArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul (ArithmeticFunction.pmul (moebius : ArithmeticFunction ℝ) (moebius : ArithmeticFunction ℝ)) reciprocalSquareArithmetic

lemma reciprocalSquareArithmetic_multiplicative : reciprocalSquareArithmetic.IsMultiplicative := by
  refine ⟨by norm_num [reciprocalSquareArithmetic],?_⟩
  intro m n hmn
  simp only [reciprocalSquareArithmetic,ArithmeticFunction.coe_mk,Nat.cast_mul,mul_pow,one_div,mul_inv_rev]
  ring

lemma reciprocalFourthArithmetic_multiplicative : reciprocalFourthArithmetic.IsMultiplicative :=
  reciprocalSquareArithmetic_multiplicative.pmul reciprocalSquareArithmetic_multiplicative

lemma squarefreeReciprocalSquareArithmetic_multiplicative : squarefreeReciprocalSquareArithmetic.IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pmul reciprocalSquareArithmetic_multiplicative

lemma reciprocalFourthArithmetic_value (n : ℕ) : reciprocalFourthArithmetic n=1/(n : ℝ)^4 := by
  change (1/(n : ℝ)^2)*(1/(n : ℝ)^2)=1/(n : ℝ)^4
  ring

lemma squarefreeReciprocalSquareArithmetic_value (n : ℕ) :
    squarefreeReciprocalSquareArithmetic n=((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 := by
  change (((moebius n : ℤ) : ℝ)*((moebius n : ℤ) : ℝ))*(1/(n : ℝ)^2)=((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2
  ring

lemma reciprocalSquareArithmetic_norm_summable : Summable (fun n : ℕ => ‖reciprocalSquareArithmetic n‖) := by
  have he (n : ℕ) : ‖reciprocalSquareArithmetic n‖=1/(n : ℝ)^2 := by
    change ‖1/(n : ℝ)^2‖=1/(n : ℝ)^2
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  simpa only [he] using hasSum_zeta_two.summable

lemma reciprocalFourthArithmetic_norm_summable : Summable (fun n : ℕ => ‖reciprocalFourthArithmetic n‖) := by
  simpa [reciprocalFourthArithmetic_value,Real.norm_eq_abs] using hasSum_zeta_four.summable

lemma squarefreeReciprocalSquareArithmetic_norm_summable : Summable (fun n : ℕ => ‖squarefreeReciprocalSquareArithmetic n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hasSum_zeta_two.summable
  intro n
  rw [squarefreeReciprocalSquareArithmetic_value,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hmu : ((moebius n : ℤ) : ℝ)^2≤1 := by
    rcases moebius_eq_or n with h|h|h <;> rw [h] <;> norm_num
  exact div_le_div_of_nonneg_right hmu (sq_nonneg _)

lemma reciprocalSquareArithmetic_prime_power (p k : ℕ) :
    reciprocalSquareArithmetic (p^k)=(1/(p : ℝ)^2)^k := by
  simp only [reciprocalSquareArithmetic,ArithmeticFunction.coe_mk,Nat.cast_pow,one_div,inv_pow,←pow_mul,mul_comm]

lemma reciprocalFourthArithmetic_prime_power (p k : ℕ) :
    reciprocalFourthArithmetic (p^k)=(1/(p : ℝ)^4)^k := by
  simp only [reciprocalFourthArithmetic_value,Nat.cast_pow,one_div,inv_pow,←pow_mul,mul_comm]

lemma squarefreeReciprocalSquareArithmetic_prime_power_tsum (p : ℕ) (hp : Nat.Prime p) :
    (∑' k : ℕ,squarefreeReciprocalSquareArithmetic (p^k))=1+1/(p : ℝ)^2 := by
  have hz (k : ℕ) (hk : k∉Finset.range 2) : squarefreeReciprocalSquareArithmetic (p^k)=0 := by
    have hk2 : 2≤k := by simp only [Finset.mem_range] at hk;omega
    rw [squarefreeReciprocalSquareArithmetic_value,moebius_apply_prime_pow hp (by omega),if_neg (by omega)]
    norm_num
  rw [tsum_eq_sum hz]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    squarefreeReciprocalSquareArithmetic_value,moebius_apply_one,moebius_apply_prime hp]
  norm_num

lemma reciprocal_power_local_lt_one (p k : ℕ) (hp : Nat.Prime p) (hk : 1≤k) :
    |1/(p : ℝ)^k|<1 := by
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
  have hpow : (1 : ℝ)<(p : ℝ)^k := one_lt_pow₀ (by linarith) (by omega)
  rw [abs_of_nonneg (by positivity)]
  exact (div_lt_one (by positivity)).mpr hpow

theorem squarefree_reciprocal_square_series :
    (∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)=15/Real.pi^2 := by
  have hf := squarefreeReciprocalSquareArithmetic_multiplicative.eulerProduct_hasProd squarefreeReciprocalSquareArithmetic_norm_summable
  have hg := reciprocalFourthArithmetic_multiplicative.eulerProduct_hasProd reciprocalFourthArithmetic_norm_summable
  have hh := reciprocalSquareArithmetic_multiplicative.eulerProduct_hasProd reciprocalSquareArithmetic_norm_summable
  have hloc (p : Nat.Primes) :
      (∑' k : ℕ,squarefreeReciprocalSquareArithmetic ((p : ℕ)^k))*(∑' k : ℕ,reciprocalFourthArithmetic ((p : ℕ)^k)) =
        ∑' k : ℕ,reciprocalSquareArithmetic ((p : ℕ)^k) := by
    rw [squarefreeReciprocalSquareArithmetic_prime_power_tsum p p.property]
    simp_rw [reciprocalFourthArithmetic_prime_power,reciprocalSquareArithmetic_prime_power]
    rw [(hasSum_geometric_of_abs_lt_one (reciprocal_power_local_lt_one p 4 p.property (by norm_num))).tsum_eq,
      (hasSum_geometric_of_abs_lt_one (reciprocal_power_local_lt_one p 2 p.property (by norm_num))).tsum_eq]
    have hp2 : (2 : ℝ)≤(p : ℕ) := by exact_mod_cast p.property.two_le
    have hp0 : ((p : ℕ) : ℝ)≠0 := by linarith
    have hden2 : 1-1/((p : ℕ) : ℝ)^2≠0 := by
      have ht := reciprocal_power_local_lt_one p 2 p.property (by norm_num)
      rw [abs_of_nonneg (by positivity)] at ht
      linarith
    have hden4 : 1-1/((p : ℕ) : ℝ)^4≠0 := by
      have ht := reciprocal_power_local_lt_one p 4 p.property (by norm_num)
      rw [abs_of_nonneg (by positivity)] at ht
      linarith
    rw [←div_eq_mul_inv]
    apply (div_eq_iff hden4).mpr
    rw [mul_comm,←div_eq_mul_inv]
    apply (eq_div_iff hden2).mpr
    field_simp [hp0] <;> ring
  have hfg := hf.mul hg
  have he : (∑' n : ℕ,squarefreeReciprocalSquareArithmetic n)*(∑' n : ℕ,reciprocalFourthArithmetic n) =
      ∑' n : ℕ,reciprocalSquareArithmetic n := by
    have hfg' : HasProd (fun p : Nat.Primes => ∑' k : ℕ,reciprocalSquareArithmetic ((p : ℕ)^k))
        ((∑' n : ℕ,squarefreeReciprocalSquareArithmetic n)*(∑' n : ℕ,reciprocalFourthArithmetic n)) := by
      simpa only [hloc] using hfg
    exact hfg'.unique hh
  simp_rw [squarefreeReciprocalSquareArithmetic_value,reciprocalFourthArithmetic_value] at he
  change (∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)*(∑' n : ℕ,1/(n : ℝ)^4) = ∑' n : ℕ,1/(n : ℝ)^2 at he
  rw [hasSum_zeta_four.tsum_eq,hasSum_zeta_two.tsum_eq] at he
  have hpi : Real.pi≠0 := Real.pi_ne_zero
  have h : (∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)=(Real.pi^2/6)/(Real.pi^4/90) :=
    (eq_div_iff (by positivity)).mpr he
  rw [h]
  field_simp [hpi] <;> ring

theorem squarefree_reciprocal_square_series_le_152 :
    (∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)≤(38/25 : ℝ) := by
  rw [squarefree_reciprocal_square_series]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<Real.pi^2)).mpr
  nlinarith [Real.pi_gt_d4,Real.pi_pos]

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
open Finset Nat ArithmeticFunction Real Set
open scoped BigOperators Classical

namespace Helfgott

lemma moebius_real_square_nonneg (n : ℕ) : 0 ≤ ((moebius n : ℤ) : ℝ)^2 := sq_nonneg _

lemma moebius_real_square_le_one (n : ℕ) : ((moebius n : ℤ) : ℝ)^2 ≤ 1 := by
  rcases moebius_eq_or n with h|h|h <;> rw [h] <;> norm_num

lemma moebius_real_square_eq_zero_four_dvd (n : ℕ) (hn : 4 ∣ n) :
    ((moebius n : ℤ) : ℝ)^2=0 := by
  have hs : ¬Squarefree n := by
    intro h
    have hunit : IsUnit (2 : ℕ) := h 2 (by simpa using hn)
    norm_num at hunit
  rw [moebius_eq_zero_of_not_squarefree hs]
  norm_num

lemma squarefree_count_le_three_quarters (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2) ≤ 3/4*(N : ℝ)+1 := by
  have hp (n : ℕ) : ((moebius n : ℤ) : ℝ)^2 ≤ if 4 ∣ n then (0 : ℝ) else 1 := by
    by_cases hn : 4 ∣ n
    · simp only [if_pos hn,moebius_real_square_eq_zero_four_dvd n hn,le_refl]
    · simpa only [if_neg hn] using moebius_real_square_le_one n
  have hi : (∑ n ∈ Finset.Icc 1 N,if 4 ∣ n then (0 : ℝ) else 1) =
      (N : ℝ)-((N/4 : ℕ) : ℝ) := by
    have hcard : (Finset.Icc 1 N).filter (fun n => 4 ∣ n) =
        (Finset.range (N+1)).filter (fun n => n ≠ 0 ∧ 4 ∣ n) := by
      ext n
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
      omega
    have he := Nat.card_multiples' N 4
    rw [←hcard] at he
    have ht := Finset.card_filter_add_card_filter_not (s:=Finset.Icc 1 N) (p:=fun n => 4 ∣ n)
    rw [he,Nat.card_Icc] at ht
    simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const, nsmul_eq_mul,mul_one]
    have h := congrArg (fun m : ℕ => (m : ℝ)) ht
    norm_num at h
    linarith
  have hrem := Nat.mod_lt N (by norm_num : (0 : ℕ)<4)
  have hdiv := Nat.mod_add_div N 4
  have h : (N : ℝ) = ((N%4 : ℕ) : ℝ)+4*((N/4 : ℕ) : ℝ) := by exact_mod_cast hdiv.symm
  have hr : (((N%4 : ℕ) : ℝ)) ≤ 4 := by exact_mod_cast (Nat.le_of_lt hrem)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,if 4 ∣ n then (0 : ℝ) else 1 := Finset.sum_le_sum (fun n hn => hp n)
    _ = (N : ℝ)-((N/4 : ℕ) : ℝ) := hi
    _ ≤ _ := by linarith

lemma shifted_reciprocal_square_tsum_lower (K : ℕ) :
    1/((K+1 : ℕ) : ℝ) ≤ ∑' n : ℕ,1/((n+K+1 : ℕ) : ℝ)^2 := by
  have anti : AntitoneOn (fun t : ℝ => t^(-2 : ℝ)) (Set.Ici ((K+1 : ℕ) : ℝ)) := by
    intro a ha b hb hab
    have hpos : (0 : ℝ)<((K+1 : ℕ) : ℝ) := by positivity
    exact Real.rpow_le_rpow_of_nonpos (hpos.trans_le ha) hab (by norm_num)
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-2 : ℝ)) := by
    simpa using (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  have ht := anti.integral_le_tsum_comp_add (K+1) hs (fun t ht => Real.rpow_nonneg ((by positivity : (0 : ℝ)≤((K+1 : ℕ) : ℝ)).trans ht.le) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by positivity : (0 : ℝ)<((K+1 : ℕ) : ℝ))] at ht
  norm_num [Real.rpow_neg,Real.rpow_two,Real.rpow_neg_one,one_div,Nat.add_assoc] at ht ⊢
  exact ht

lemma squarefree_reciprocal_tail_summable (N : ℕ) :
    Summable (fun n : ℕ => if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0) := by
  apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) ?_ hasSum_zeta_two.summable
  intro n
  split_ifs
  · exact div_le_div_of_nonneg_right (moebius_real_square_le_one n) (sq_nonneg _)
  · positivity

lemma reciprocal_square_tail_as_shift (N : ℕ) :
    (∑' n : ℕ,if N<n then 1/(n : ℝ)^2 else 0)=∑' n : ℕ,1/((n+N+1 : ℕ) : ℝ)^2 := by
  let f : ℕ → ℝ := fun n => if N<n then 1/(n : ℝ)^2 else 0
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun n => by dsimp [f];split_ifs <;> positivity) ?_ hasSum_zeta_two.summable
    intro n
    dsimp [f]
    split_ifs <;> first | exact le_rfl | positivity
  have he := hf.sum_add_tsum_nat_add (N+1)
  have hz : ∑ n ∈ Finset.range (N+1),f n=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnn : n≤N := by have h := Finset.mem_range.mp hn;omega
    exact if_neg (by omega)
  rw [hz,zero_add] at he
  rw [←he]
  apply tsum_congr
  intro n
  simp only [f,if_pos (by omega : N<n+(N+1)),Nat.add_assoc]

theorem squarefree_reciprocal_tail_upper (N : ℕ) (hN : 1≤N) :
    (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0) ≤
      1/(N : ℝ)-1/(16*((N/4+1 : ℕ) : ℝ)) := by
  let r : ℕ → ℝ := fun n => if N<n then (1-((moebius n : ℤ) : ℝ)^2)/(n : ℝ)^2 else 0
  have hn (n : ℕ) : 0≤r n := by dsimp [r];split_ifs <;> positivity [sub_nonneg.mpr (moebius_real_square_le_one n)]
  have hr : Summable r := by
    apply Summable.of_nonneg_of_le hn ?_ hasSum_zeta_two.summable
    intro n
    dsimp [r]
    split_ifs
    · exact div_le_div_of_nonneg_right (by nlinarith [moebius_real_square_nonneg n]) (sq_nonneg _)
    · positivity
  let sparseMap : ℕ → ℕ := fun k => 4*(k+N/4+1)
  have hi : Function.Injective sparseMap := by intro k l h;dsimp [sparseMap] at h;omega
  have hpoint (k : ℕ) : r (sparseMap k)=(1/16 : ℝ)*(1/((k+N/4+1 : ℕ) : ℝ)^2) := by
    have hd : 4 ∣ sparseMap k := by dsimp [sparseMap];exact dvd_mul_right _ _
    have hb : N<sparseMap k := by
      dsimp [sparseMap]
      have hm := Nat.mod_lt N (by norm_num : (0 : ℕ)<4)
      have he := Nat.mod_add_div N 4
      omega
    dsimp [r]
    rw [if_pos hb,moebius_real_square_eq_zero_four_dvd (sparseMap k) hd]
    simp only [sparseMap,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    simp only [mul_pow,one_div,mul_inv_rev]
    norm_num
    ring
  have hl := tsum_comp_le_tsum_of_inj hr hn hi
  simp only [Function.comp_def,hpoint,tsum_mul_left] at hl
  have ht := shifted_reciprocal_square_tsum_lower (N/4)
  have hlow : 1/(16*((N/4+1 : ℕ) : ℝ)) ≤ ∑' n : ℕ,r n := by
    have h := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ)≤1/16)
    calc _ = (1/16 : ℝ)*(1/((N/4+1 : ℕ) : ℝ)) := by ring
         _ ≤ _ := h.trans hl
  have hf := squarefree_reciprocal_tail_summable N
  have hadd := hf.tsum_add hr
  have he : (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)+(∑' n : ℕ,r n)=
      ∑' n : ℕ,1/((n+N+1 : ℕ) : ℝ)^2 := by
    rw [←reciprocal_square_tail_as_shift N,←hadd]
    apply tsum_congr
    intro n
    dsimp [r]
    split_ifs <;> ring
  have hup := shifted_reciprocal_square_tsum_le N hN
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 100000
open Finset Nat ArithmeticFunction
open scoped BigOperators

namespace Helfgott

def smoothSquarefreeCountRat (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 1 N,if Squarefree n then (1 : ℚ) else 0

def smoothSquarefreePartialRat (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 1 N,if Squarefree n then 1/(n : ℚ)^2 else 0

lemma squarefree_smooth_finite_certificate :
    ∀ N ∈ Finset.range 16,
      0≤(38/25 : ℚ)-smoothSquarefreePartialRat N ∧
      smoothSquarefreeCountRat N+(1/2 : ℚ)*(N : ℚ)^2*((38/25 : ℚ)-smoothSquarefreePartialRat N)≤(127/100 : ℚ)*N ∧
      smoothSquarefreeCountRat N+(1/2 : ℚ)*(N+1 : ℚ)^2*((38/25 : ℚ)-smoothSquarefreePartialRat N)≤(127/100 : ℚ)*(N+1) := by
  decide +kernel

lemma moebius_real_square_indicator (n : ℕ) :
    ((moebius n : ℤ) : ℝ)^2=if Squarefree n then (1 : ℝ) else 0 := by
  by_cases hn : Squarefree n
  · rw [if_pos hn]
    exact_mod_cast moebius_sq_eq_one_of_squarefree hn
  · rw [if_neg hn,moebius_eq_zero_of_not_squarefree hn]
    norm_num

lemma smoothSquarefreeCountRat_cast (N : ℕ) :
    (smoothSquarefreeCountRat N : ℝ)=∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2 := by
  unfold smoothSquarefreeCountRat
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [moebius_real_square_indicator]
  split_ifs <;> norm_num

lemma smoothSquarefreePartialRat_cast (N : ℕ) :
    (smoothSquarefreePartialRat N : ℝ)=∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 := by
  unfold smoothSquarefreePartialRat
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [moebius_real_square_indicator]
  split_ifs <;> norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_reciprocal_tail_sub (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2)+
    (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0) =
    ∑' n : ℕ,((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 := by
  let f : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) ?_ hasSum_zeta_two.summable
    intro n
    exact div_le_div_of_nonneg_right (moebius_real_square_le_one n) (sq_nonneg _)
  have he := hf.sum_add_tsum_nat_add (N+1)
  have hs : (∑ n ∈ Finset.range (N+1),f n)=∑ n ∈ Finset.Icc 1 N,f n := by
    rw [Finset.range_eq_Ico]
    have hi : Finset.Ico 0 (N+1)=insert 0 (Finset.Icc 1 N) := by ext n;simp;omega
    rw [hi,Finset.sum_insert (by simp)]
    simp [f]
  rw [hs] at he
  have ht : (∑' n : ℕ,if N<n then f n else 0)=∑' n : ℕ,f (n+(N+1)) := by
    have hfi := squarefree_reciprocal_tail_summable N
    have het := hfi.sum_add_tsum_nat_add (N+1)
    have hz : (∑ n ∈ Finset.range (N+1),if N<n then f n else 0)=0 := by
      apply Finset.sum_eq_zero
      intro n hn
      exact if_neg (by have h := Finset.mem_range.mp hn;omega)
    rw [hz,zero_add] at het
    rw [←het]
    apply tsum_congr
    intro n
    rw [if_pos (by omega : N<n+(N+1))]
  change (∑ n ∈ Finset.Icc 1 N,f n)+(∑' n : ℕ,if N<n then f n else 0)=∑' n : ℕ,f n
  rw [ht]
  exact he

lemma squarefree_smooth_small (x : ℝ) (N : ℕ) (hN : N<16)
    (hlo : (N : ℝ)≤x) (hhi : x≤(N : ℝ)+1) :
    (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2)+
    (x^2/2)*(∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(127/100 : ℝ)*x := by
  rcases squarefree_smooth_finite_certificate N (Finset.mem_range.mpr hN) with ⟨hc,ha,hb⟩
  let a : ℝ := smoothSquarefreeCountRat N
  let c : ℝ := (38/25 : ℝ)-smoothSquarefreePartialRat N
  have hc' : 0≤c := by
    have h := (Rat.cast_le (K:=ℝ)).mpr hc
    push_cast at h
    simpa [c] using h
  have ha' : a+(1/2 : ℝ)*(N : ℝ)^2*c≤(127/100 : ℝ)*N := by
    have h := (Rat.cast_le (K:=ℝ)).mpr ha
    push_cast at h
    simpa [a,c] using h
  have hb' : a+(1/2 : ℝ)*((N : ℝ)+1)^2*c≤(127/100 : ℝ)*((N : ℝ)+1) := by
    have h := (Rat.cast_le (K:=ℝ)).mpr hb
    push_cast at h
    simpa [a,c] using h
  have hqa : a+(1/2 : ℝ)*(N : ℝ)^2*c-(127/100 : ℝ)*N≤0 := by linarith
  have hqb : a+(1/2 : ℝ)*((N : ℝ)+1)^2*c-(127/100 : ℝ)*((N : ℝ)+1)≤0 := by linarith
  have hleft := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤(N : ℝ)+1-x) hqa
  have hright := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤x-(N : ℝ)) hqb
  have hquad : 0≤c*(x-(N : ℝ))*((N : ℝ)+1-x) := mul_nonneg (mul_nonneg hc' (by linarith)) (by linarith)
  have hpoly : a+(x^2/2)*c≤(127/100 : ℝ)*x := by nlinarith
  have htail := squarefree_reciprocal_tail_sub N
  have htotal := squarefree_reciprocal_square_series_le_152
  have hle : (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤c := by
    dsimp [c]
    rw [smoothSquarefreePartialRat_cast]
    linarith
  rw [←smoothSquarefreeCountRat_cast]
  have hm : (x^2/2)*(∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(x^2/2)*c :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  exact (add_le_add_right hm a).trans (by simpa only [add_comm] using hpoly)

lemma squarefree_smooth_large (x : ℝ) (N : ℕ) (hx : 16≤x)
    (hlo : (N : ℝ)≤x) (hhi : x≤(N : ℝ)+1) :
    (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2)+
    (x^2/2)*(∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(127/100 : ℝ)*x := by
  have hN : 1≤N := by
    by_contra h
    have he : N=0 := by omega
    norm_num [he] at hhi
    linarith
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  have hx1 : 0<x-1 := by linarith
  have hx4 : 0<x+4 := by linarith
  have hdiv : 4*((N/4 : ℕ) : ℝ)≤(N : ℝ) := by exact_mod_cast (Nat.mul_div_le N 4)
  have hden : 16*((N/4+1 : ℕ) : ℝ)≤4*(x+4) := by push_cast;linarith
  have hupper := one_div_le_one_div_of_le hx1 (by linarith : x-1≤(N : ℝ))
  have hlower := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<16*((N/4+1 : ℕ) : ℝ)) hden
  have ht : (∑' n : ℕ,if N<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤1/(x-1)-1/(4*(x+4)) := by
    have h := squarefree_reciprocal_tail_upper N hN
    linarith
  have hc : (∑ n ∈ Finset.Icc 1 N,((moebius n : ℤ) : ℝ)^2)≤3/4*x+1 := by
    have h := squarefree_count_le_three_quarters N
    linarith
  have hid : (3/4 : ℝ)*x+1+(x^2/2)*(1/(x-1)-1/(4*(x+4)))=
      (9/8 : ℝ)*x+2+1/(2*(x-1))-2/(x+4) := by
    field_simp [hx1.ne',hx4.ne']
    ring
  have hsmall : 1/(2*(x-1))≤(1/30 : ℝ) := one_div_le_one_div_of_le (by norm_num) (by linarith)
  calc
    _ ≤ (3/4 : ℝ)*x+1+(x^2/2)*(1/(x-1)-1/(4*(x+4))) := add_le_add hc (mul_le_mul_of_nonneg_left ht (by positivity))
    _ = (9/8 : ℝ)*x+2+1/(2*(x-1))-2/(x+4) := hid
    _ ≤ (9/8 : ℝ)*x+2+1/30 := by
      have hp : 0≤2/(x+4) := by positivity
      linarith
    _ ≤ _ := by linarith

theorem squarefree_smoothed_count_le_127 (x : ℝ) (hx : 0≤x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,((moebius n : ℤ) : ℝ)^2)+
    (x^2/2)*(∑' n : ℕ,if ⌊x⌋₊<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(127/100 : ℝ)*x := by
  have hlo := Nat.floor_le hx
  have hhi := (Nat.lt_floor_add_one x).le
  by_cases h : 16≤x
  · exact squarefree_smooth_large x ⌊x⌋₊ h hlo hhi
  · have hN : ⌊x⌋₊<16 := by
      by_contra hN
      have hc : (16 : ℝ)≤⌊x⌋₊ := by exact_mod_cast (Nat.le_of_not_gt hN)
      linarith
    exact squarefree_smooth_small x ⌊x⌋₊ hN hlo hhi

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

theorem squarefree_coprime_count_square_root_error (q N : ℕ) (hq : q ≠ 0) :
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

section
set_option autoImplicit false
set_option maxHeartbeats 2300000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma moebius_real_abs_eq_square (n : ℕ) : |((moebius n : ℤ) : ℝ)|=((moebius n : ℤ) : ℝ)^2 := by
  rcases moebius_eq_or n with h|h|h <;> rw [h] <;> norm_num

lemma nat_div_interval_cast_error_le_one (A B k : ℕ) (hk : 0<k) :
    |((B/k : ℕ) : ℝ)-((A/k : ℕ) : ℝ)-((B : ℝ)-(A : ℝ))/(k : ℝ)|≤1 := by
  have ha := nat_div_cast_error_le_one A k hk
  have hb := nat_div_cast_error_le_one B k hk
  have hal : ((A/k : ℕ) : ℝ)≤(A : ℝ)/(k : ℝ) := Nat.cast_div_le
  have hbl : ((B/k : ℕ) : ℝ)≤(B : ℝ)/(k : ℝ) := Nat.cast_div_le
  rw [abs_of_nonpos (sub_nonpos.mpr hal)] at ha
  rw [abs_of_nonpos (sub_nonpos.mpr hbl)] at hb
  rw [sub_div,abs_le]
  constructor <;> linarith

lemma coprime_moebius_density_tail_squarefree (q D : ℕ) (hq : q≠0) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹-
      (∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)|≤
      ∑' n : ℕ,if D<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0 := by
  let f : ℕ → ℝ := fun n => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0
  let g : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2
  have hf : Summable f := coprime_moebius_reciprocal_square_summable q
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le (fun n => by dsimp [g];positivity) ?_ hasSum_zeta_two.summable
    intro n
    exact div_le_div_of_nonneg_right (moebius_real_square_le_one n) (sq_nonneg _)
  have hs : (∑ d ∈ Finset.range (D+1),f d) = ∑ d ∈ Finset.Icc 1 D,f d := by
    rw [Finset.range_eq_Ico]
    have hi : Finset.Ico 0 (D+1)=insert 0 (Finset.Icc 1 D) := by ext n;simp;omega
    rw [hi,Finset.sum_insert (by simp)]
    simp [f]
  have he := hf.sum_add_tsum_nat_add (D+1)
  rw [hs] at he
  rw [←squarefree_coprime_density_series q hq]
  change |(∑' n : ℕ,f n)-(∑ d ∈ Finset.Icc 1 D,f d)|≤_
  have hid : (∑' n : ℕ,f n)-(∑ d ∈ Finset.Icc 1 D,f d)=∑' n : ℕ,f (n+(D+1)) := by linarith
  rw [hid]
  have hft : Summable (fun n : ℕ => f (n+(D+1))) := hf.comp_injective (fun n m h => by omega)
  have hgt : Summable (fun n : ℕ => g (n+(D+1))) := hg.comp_injective (fun n m h => by omega)
  have hpoint (n : ℕ) : ‖f n‖≤g n := by
    dsimp [f,g]
    by_cases hc : Nat.Coprime n q
    · rw [if_pos hc,abs_div,show |(n : ℝ)^2|=(n : ℝ)^2 from abs_of_nonneg (sq_nonneg _),moebius_real_abs_eq_square]
    · rw [if_neg hc,abs_zero]
      positivity
  have hbound : |∑' n : ℕ,f (n+(D+1))|≤∑' n : ℕ,g (n+(D+1)) :=
    (show |∑' n : ℕ,f (n+(D+1))|≤∑' n : ℕ,‖f (n+(D+1))‖ by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hft.norm).trans
      (hft.norm.tsum_le_tsum (fun n => hpoint (n+(D+1))) hgt)
  have hgf := hg.sum_add_tsum_nat_add (D+1)
  have hgs : (∑ d ∈ Finset.range (D+1),g d)=∑ d ∈ Finset.Icc 1 D,g d := by
    rw [Finset.range_eq_Ico]
    have hi : Finset.Ico 0 (D+1)=insert 0 (Finset.Icc 1 D) := by ext n;simp;omega
    rw [hi,Finset.sum_insert (by simp)]
    simp [g]
  rw [hgs] at hgf
  have hge := squarefree_reciprocal_tail_sub D
  change (∑ d ∈ Finset.Icc 1 D,g d)+(∑' n : ℕ,if D<n then g n else 0)=∑' n : ℕ,g n at hge
  have htail : (∑' n : ℕ,g (n+(D+1)))=∑' n : ℕ,if D<n then g n else 0 := by linarith
  rw [htail] at hbound
  exact hbound

lemma floor_sqrt_rational_nat (B e : ℕ) (he : 1≤e) :
    ⌊Real.sqrt ((B : ℝ)/(e : ℝ))⌋₊=(B/e).sqrt := by
  let D := (B/e).sqrt
  have heR : (0 : ℝ)<e := by exact_mod_cast he
  have hlo : ((B/e : ℕ) : ℝ)≤(B : ℝ)/(e : ℝ) := Nat.cast_div_le
  have hmod : ((B%e : ℕ) : ℝ)<(e : ℝ) := by exact_mod_cast Nat.mod_lt B (by omega : 0<e)
  have hid : (e : ℝ)*((B/e : ℕ) : ℝ)+((B%e : ℕ) : ℝ)=(B : ℝ) := by exact_mod_cast Nat.div_add_mod B e
  have hhi : (B : ℝ)/(e : ℝ)<((B/e : ℕ) : ℝ)+1 := (div_lt_iff₀ heR).mpr (by nlinarith)
  have hDlo : (D : ℝ)^2≤(B : ℝ)/(e : ℝ) :=
    (show (D : ℝ)^2≤((B/e : ℕ) : ℝ) by exact_mod_cast Nat.sqrt_le' (B/e)).trans hlo
  have hDhi : (B : ℝ)/(e : ℝ)<((D : ℝ)+1)^2 := by
    have h : ((B/e : ℕ) : ℝ)+1≤((D : ℝ)+1)^2 := by
      exact_mod_cast Nat.lt_succ_sqrt' (B/e)
    exact hhi.trans_le h
  apply (Nat.floor_eq_iff (Real.sqrt_nonneg _)).mpr
  constructor
  · simpa only [Real.sqrt_sq (by positivity : (0 : ℝ)≤D)] using Real.sqrt_le_sqrt hDlo
  · simpa only [Real.sqrt_sq (by positivity : (0 : ℝ)≤(D : ℝ)+1)] using Real.sqrt_lt_sqrt (by positivity) hDhi

theorem squarefree_coprime_rational_interval_floor_error (q A B e : ℕ)
    (hq : q≠0) (he : 1≤e) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
      ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0)-
      (((B : ℝ)-(A : ℝ))/(e : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)|≤
      (127/100 : ℝ)*Real.sqrt ((B : ℝ)/(e : ℝ)) := by
  let X : ℝ := (B : ℝ)/(e : ℝ)
  let Y : ℝ := ((B : ℝ)-(A : ℝ))/(e : ℝ)
  let D : ℕ := (B/e).sqrt
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  let P : ℝ := ∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0
  let S : ℝ := ∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
      ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0
  let T : ℝ := ∑' n : ℕ,if D<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0
  have hY : 0≤Y := by
    dsimp [Y]
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hAB)) (by positivity)
  have hYX : Y≤X/2 := by
    have h : (B : ℝ)≤2*(A : ℝ) := by exact_mod_cast hhalf
    have heR : (0 : ℝ)<e := by exact_mod_cast he
    dsimp [Y,X]
    apply (div_le_iff₀ heR).mpr
    field_simp
    linarith
  have hT : 0≤T := by
    dsimp [T]
    apply tsum_nonneg
    intro n
    split_ifs <;> positivity
  have herr : |S-Y*P|≤∑ d ∈ Finset.Icc 1 D,((moebius d : ℤ) : ℝ)^2 := by
    dsimp [S,P]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,if_pos hc]
      have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
      have hid : ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ))-Y*(((moebius d : ℤ) : ℝ)/(d : ℝ)^2)=
          ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)-((B : ℝ)-(A : ℝ))/((d^2*e : ℕ) : ℝ)) := by
        dsimp [Y]
        push_cast
        field_simp <;> ring
      rw [hid,abs_mul,moebius_real_abs_eq_square]
      exact mul_le_of_le_one_right (sq_nonneg _) (nat_div_interval_cast_error_le_one A B _ (Nat.mul_pos (pow_pos (Finset.mem_Icc.mp hd).1 2) he))
    · simp only [if_neg hc,mul_zero,sub_zero,abs_zero]
      positivity
  have htail : |P-C|≤T := by
    simpa only [abs_sub_comm] using coprime_moebius_density_tail_squarefree q D hq
  have hbound : |S-Y*C|≤(∑ d ∈ Finset.Icc 1 D,((moebius d : ℤ) : ℝ)^2)+(X/2)*T := by
    have hid : S-Y*C=(S-Y*P)+Y*(P-C) := by ring
    rw [hid]
    refine (abs_add_le _ _).trans (add_le_add herr ?_)
    rw [abs_mul,abs_of_nonneg hY]
    exact (mul_le_mul_of_nonneg_left htail hY).trans (mul_le_mul_of_nonneg_right hYX hT)
  have hsm := squarefree_smoothed_count_le_127 (Real.sqrt X) (Real.sqrt_nonneg X)
  have hfloor : ⌊Real.sqrt X⌋₊=D := floor_sqrt_rational_nat B e he
  rw [hfloor,Real.sq_sqrt (by dsimp [X];positivity)] at hsm
  change |S-Y*C|≤_
  exact hbound.trans hsm

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2500000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma real_floor_interval_error_le_one (A B k : ℝ) (hA : 0≤A) (hB : 0≤B) (hk : 0<k) :
    |(⌊B/k⌋₊ : ℝ)-(⌊A/k⌋₊ : ℝ)-(B-A)/k|≤1 := by
  have hal := Nat.floor_le (div_nonneg hA hk.le)
  have hbl := Nat.floor_le (div_nonneg hB hk.le)
  have hau := Nat.lt_floor_add_one (A/k)
  have hbu := Nat.lt_floor_add_one (B/k)
  rw [sub_div,abs_le]
  constructor <;> linarith

lemma floor_sqrt_nonnegative_real (X : ℝ) (hX : 0≤X) :
    ⌊Real.sqrt X⌋₊=Nat.sqrt ⌊X⌋₊ := by
  let D := Nat.sqrt ⌊X⌋₊
  have hlo : (⌊X⌋₊ : ℝ)≤X := Nat.floor_le hX
  have hhi : X<(⌊X⌋₊ : ℝ)+1 := Nat.lt_floor_add_one X
  have hDlo : (D : ℝ)^2≤X :=
    (show (D : ℝ)^2≤(⌊X⌋₊ : ℝ) by exact_mod_cast Nat.sqrt_le' ⌊X⌋₊).trans hlo
  have hDhi : X<((D : ℝ)+1)^2 := by
    have h : (⌊X⌋₊ : ℝ)+1≤((D : ℝ)+1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' ⌊X⌋₊
    exact hhi.trans_le h
  apply (Nat.floor_eq_iff (Real.sqrt_nonneg _)).mpr
  constructor
  · simpa only [Real.sqrt_sq (by positivity : (0 : ℝ)≤D)] using Real.sqrt_le_sqrt hDlo
  · simpa only [Real.sqrt_sq (by positivity : (0 : ℝ)≤(D : ℝ)+1)] using Real.sqrt_lt_sqrt hX hDhi

lemma floor_sqrt_real_quotient (B : ℝ) (e : ℕ) (hB : 0≤B) (he : 1≤e) :
    ⌊Real.sqrt (B/(e : ℝ))⌋₊=(⌊B⌋₊/e).sqrt := by
  rw [floor_sqrt_nonnegative_real (B/(e : ℝ)) (div_nonneg hB (by positivity)),Nat.floor_div_natCast]

theorem squarefree_coprime_real_rational_interval_floor_error (q e : ℕ) (A B : ℝ)
    (hq : q≠0) (he : 1≤e) (hA : 0≤A) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
      ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0)-
      ((B-A)/(e : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)|≤
      (127/100 : ℝ)*Real.sqrt (B/(e : ℝ)) := by
  have hB : 0≤B := hA.trans hAB
  let X : ℝ := B/(e : ℝ)
  let Y : ℝ := (B-A)/(e : ℝ)
  let D : ℕ := (⌊B⌋₊/e).sqrt
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  let P : ℝ := ∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0
  let S : ℝ := ∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
      ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0
  let T : ℝ := ∑' n : ℕ,if D<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0
  have hY : 0≤Y := by
    dsimp [Y]
    exact div_nonneg (sub_nonneg.mpr (hAB)) (by positivity)
  have hYX : Y≤X/2 := by
    have h : B≤2*A := hhalf
    have heR : (0 : ℝ)<e := by exact_mod_cast he
    dsimp [Y,X]
    apply (div_le_iff₀ heR).mpr
    field_simp
    linarith
  have hT : 0≤T := by
    dsimp [T]
    apply tsum_nonneg
    intro n
    split_ifs <;> positivity
  have herr : |S-Y*P|≤∑ d ∈ Finset.Icc 1 D,((moebius d : ℤ) : ℝ)^2 := by
    dsimp [S,P]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,if_pos hc]
      have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
      have hid : ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ))-Y*(((moebius d : ℤ) : ℝ)/(d : ℝ)^2)=
          ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)-(B-A)/((d^2*e : ℕ) : ℝ)) := by
        dsimp [Y]
        push_cast
        field_simp <;> ring
      rw [hid,abs_mul,moebius_real_abs_eq_square]
      have hkpos : (0 : ℝ)<((d^2*e : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (pow_pos (Finset.mem_Icc.mp hd).1 2) he
      have hfloor := real_floor_interval_error_le_one A B ((d^2*e : ℕ) : ℝ) hA hB hkpos
      rw [Nat.floor_div_natCast,Nat.floor_div_natCast] at hfloor
      exact mul_le_of_le_one_right (sq_nonneg _) hfloor
    · simp only [if_neg hc,mul_zero,sub_zero,abs_zero]
      positivity
  have htail : |P-C|≤T := by
    simpa only [abs_sub_comm] using coprime_moebius_density_tail_squarefree q D hq
  have hbound : |S-Y*C|≤(∑ d ∈ Finset.Icc 1 D,((moebius d : ℤ) : ℝ)^2)+(X/2)*T := by
    have hid : S-Y*C=(S-Y*P)+Y*(P-C) := by ring
    rw [hid]
    refine (abs_add_le _ _).trans (add_le_add herr ?_)
    rw [abs_mul,abs_of_nonneg hY]
    exact (mul_le_mul_of_nonneg_left htail hY).trans (mul_le_mul_of_nonneg_right hYX hT)
  have hsm := squarefree_smoothed_count_le_127 (Real.sqrt X) (Real.sqrt_nonneg X)
  have hfloor : ⌊Real.sqrt X⌋₊=D := floor_sqrt_real_quotient B e hB he
  rw [hfloor,Real.sq_sqrt (div_nonneg hB (by positivity))] at hsm
  change |S-Y*C|≤_
  exact hbound.trans hsm

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2300000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_coprime_count_reordered_cap (q A B : ℕ) (hq : q≠0) (hAB : A≤B) :
    (∑ n ∈ Finset.Icc 1 A,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)=
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*
        (∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((A/(d^2*e) : ℕ) : ℝ) else 0) := by
  rw [squarefree_coprime_count_reordered q A hq]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.sqrt_le_sqrt (Nat.div_le_div_right hAB))⟩
  · intro d hd hnot
    have hdlarge : (A/e).sqrt<d := by
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hnot' : ¬(1≤d ∧ d≤(A/e).sqrt) := by simpa only [Finset.mem_Icc] using hnot
      omega
    have hd2 : A/e<d^2 := Nat.sqrt_lt'.mp hdlarge
    have hdiv : A/(d^2*e)=(A/e)/d^2 := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm]
    rw [hdiv,Nat.div_eq_of_lt hd2]
    simp

theorem squarefree_coprime_short_interval_error (q A B : ℕ) (hq : q≠0)
    (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc A B,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      ((B : ℝ)-(A : ℝ))*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt (B : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ)) := by
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hs : (∑ n ∈ Finset.Ioc A B,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)=
      (∑ n ∈ Finset.Icc 1 B,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (∑ n ∈ Finset.Icc 1 A,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) := by
    have hsub : Finset.Icc 1 A⊆Finset.Icc 1 B := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hAB⟩
    have hi : Finset.Icc 1 B \ Finset.Icc 1 A=Finset.Ioc A B := by ext n;simp;omega
    rw [←Finset.sum_sdiff hsub,hi]
    ring
  have hmain : ((B : ℝ)-(A : ℝ))*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))=
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*(((B : ℝ)-(A : ℝ))/(e : ℝ))*C := by
    have h := squarefree_coprime_density_normalization q hq
    change ((q.totient : ℝ)/(q : ℝ))*C=_ at h
    rw [mul_assoc,←h,←moebius_reciprocal_divisor_sum_totient q hq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [hs,squarefree_coprime_count_reordered q B hq,squarefree_coprime_count_reordered_cap q A B hq hAB,
    ←Finset.sum_sub_distrib,hmain,←Finset.sum_sub_distrib]
  have hterm (e : ℕ) :
      ((moebius e : ℤ) : ℝ)*(∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((B/(d^2*e) : ℕ) : ℝ) else 0)-
      ((moebius e : ℤ) : ℝ)*(∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((A/(d^2*e) : ℕ) : ℝ) else 0)-
      ((moebius e : ℤ) : ℝ)*(((B : ℝ)-(A : ℝ))/(e : ℝ))*C=
      ((moebius e : ℤ) : ℝ)*((∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0)-
        (((B : ℝ)-(A : ℝ))/(e : ℝ))*C) := by
    have hdifference : (∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((B/(d^2*e) : ℕ) : ℝ) else 0)-
        (∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((A/(d^2*e) : ℕ) : ℝ) else 0)=
        ∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0 := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> ring
    rw [←mul_sub,hdifference]
    ring
  simp_rw [hterm]
  calc
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)*((∑ d ∈ Finset.Icc 1 (B/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((B/(d^2*e) : ℕ) : ℝ)-((A/(d^2*e) : ℕ) : ℝ)) else 0)-
        (((B : ℝ)-(A : ℝ))/(e : ℝ))*C)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| *((127/100 : ℝ)*Real.sqrt ((B : ℝ)/(e : ℝ))) := by
      apply Finset.sum_le_sum
      intro e he
      have herr := squarefree_coprime_rational_interval_floor_error q A B e hq (Nat.pos_of_mem_divisors he) hAB hhalf
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Real.sqrt_div (by positivity)]
      ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2300000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

noncomputable def reciprocalSqrtArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n => 1/Real.sqrt (n : ℝ),by norm_num⟩

noncomputable def squarefreeReciprocalSqrtArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul (ArithmeticFunction.pmul (moebius : ArithmeticFunction ℝ) (moebius : ArithmeticFunction ℝ)) reciprocalSqrtArithmetic

lemma reciprocalSqrtArithmetic_multiplicative : reciprocalSqrtArithmetic.IsMultiplicative := by
  refine ⟨by norm_num [reciprocalSqrtArithmetic],?_⟩
  intro m n hmn
  simp only [reciprocalSqrtArithmetic,ArithmeticFunction.coe_mk,Nat.cast_mul,
    Real.sqrt_mul (by positivity : (0 : ℝ)≤m),one_div,mul_inv_rev]
  ring

lemma squarefreeReciprocalSqrtArithmetic_multiplicative : squarefreeReciprocalSqrtArithmetic.IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pmul reciprocalSqrtArithmetic_multiplicative

lemma squarefreeReciprocalSqrtArithmetic_value (n : ℕ) :
    squarefreeReciprocalSqrtArithmetic n=|((moebius n : ℤ) : ℝ)|/Real.sqrt (n : ℝ) := by
  change (((moebius n : ℤ) : ℝ)*((moebius n : ℤ) : ℝ))*(1/Real.sqrt (n : ℝ))=_
  rw [moebius_real_abs_eq_square]
  ring

lemma squarefreeReciprocalSqrtArithmetic_prime_power_sum (p k : ℕ) (hp : Nat.Prime p) (hk : 1≤k) :
    (∑ d ∈ (p^k).divisors,squarefreeReciprocalSqrtArithmetic d)=1+1/Real.sqrt (p : ℝ) := by
  rw [Nat.sum_divisors_prime_pow hp]
  have hs : (∑ j ∈ Finset.range (k+1),squarefreeReciprocalSqrtArithmetic (p^j))=
      ∑ j ∈ Finset.range 2,squarefreeReciprocalSqrtArithmetic (p^j) := by
    symm
    apply Finset.sum_subset
    · exact Finset.range_mono (by omega)
    · intro j hj hnot
      have hj2 : 2≤j := by simp only [Finset.mem_range] at hnot;omega
      rw [squarefreeReciprocalSqrtArithmetic_value,moebius_apply_prime_pow hp (by omega),if_neg (by omega)]
      norm_num
  rw [hs]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    squarefreeReciprocalSqrtArithmetic_value,moebius_apply_one,moebius_apply_prime hp]
  norm_num

theorem moebius_half_weighted_divisor_euler_product (q : ℕ) (hq : q≠0) :
    (∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ))=
      ∏ p ∈ q.primeFactors,(1+1/Real.sqrt (p : ℝ)) := by
  let f := squarefreeReciprocalSqrtArithmetic
  have hf : f.IsMultiplicative := squarefreeReciprocalSqrtArithmetic_multiplicative
  have hg := hf.mul (isMultiplicative_zeta.natCast (R:=ℝ))
  have he := hg.multiplicative_factorization (f*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) hq
  rw [ArithmeticFunction.coe_mul_zeta_apply] at he
  simp only [Finsupp.prod] at he
  change (∑ e ∈ q.divisors,f e)=∏ p ∈ q.factorization.support,(f*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p^q.factorization p) at he
  change (∑ e ∈ q.divisors,squarefreeReciprocalSqrtArithmetic e)=_ at he
  rw [←Finset.sum_congr rfl (fun e he => squarefreeReciprocalSqrtArithmetic_value e)]
  rw [he]
  apply Finset.prod_congr q.support_factorization
  intro p hp
  have hp' : p∈q.primeFactors := by simpa only [q.support_factorization] using hp
  have hprime := Nat.prime_of_mem_primeFactors hp'
  have hk : 1≤q.factorization p := by
    have hne : q.factorization p≠0 := Finsupp.mem_support_iff.mp hp
    omega
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  exact squarefreeReciprocalSqrtArithmetic_prime_power_sum p (q.factorization p) hprime hk

theorem squarefree_coprime_short_interval_euler_error (q A B : ℕ) (hq : q≠0)
    (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc A B,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      ((B : ℝ)-(A : ℝ))*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt (B : ℝ)*(∏ p ∈ q.primeFactors,(1+1/Real.sqrt (p : ℝ))) := by
  rw [←moebius_half_weighted_divisor_euler_product q hq]
  exact squarefree_coprime_short_interval_error q A B hq hAB hhalf

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_coprime_real_short_interval_error (q : ℕ) (A B : ℝ) (hq : q≠0)
    (hA : 0≤A) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (B-A)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt B*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ)) := by
  have hB : 0≤B := hA.trans hAB
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hs : (∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)=
      (∑ n ∈ Finset.Icc 1 ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (∑ n ∈ Finset.Icc 1 ⌊A⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) := by
    have hsub : Finset.Icc 1 ⌊A⌋₊⊆Finset.Icc 1 ⌊B⌋₊ := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono hAB)⟩
    have hi : Finset.Icc 1 ⌊B⌋₊ \ Finset.Icc 1 ⌊A⌋₊=Finset.Ioc ⌊A⌋₊ ⌊B⌋₊ := by ext n;simp;omega
    rw [←Finset.sum_sdiff hsub,hi]
    ring
  have hmain : (B-A)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))=
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((B-A)/(e : ℝ))*C := by
    have h := squarefree_coprime_density_normalization q hq
    change ((q.totient : ℝ)/(q : ℝ))*C=_ at h
    rw [mul_assoc,←h,←moebius_reciprocal_divisor_sum_totient q hq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [hs,squarefree_coprime_count_reordered q ⌊B⌋₊ hq,squarefree_coprime_count_reordered_cap q ⌊A⌋₊ ⌊B⌋₊ hq (Nat.floor_mono hAB),
    ←Finset.sum_sub_distrib,hmain,←Finset.sum_sub_distrib]
  have hterm (e : ℕ) :
      ((moebius e : ℤ) : ℝ)*(∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((⌊B⌋₊/(d^2*e) : ℕ) : ℝ) else 0)-
      ((moebius e : ℤ) : ℝ)*(∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((⌊A⌋₊/(d^2*e) : ℕ) : ℝ) else 0)-
      ((moebius e : ℤ) : ℝ)*((B-A)/(e : ℝ))*C=
      ((moebius e : ℤ) : ℝ)*((∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0)-
        ((B-A)/(e : ℝ))*C) := by
    have hdifference : (∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((⌊B⌋₊/(d^2*e) : ℕ) : ℝ) else 0)-
        (∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((⌊A⌋₊/(d^2*e) : ℕ) : ℝ) else 0)=
        ∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0 := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> ring
    rw [←mul_sub,hdifference]
    ring
  simp_rw [hterm]
  calc
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)*((∑ d ∈ Finset.Icc 1 (⌊B⌋₊/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(((⌊B⌋₊/(d^2*e) : ℕ) : ℝ)-((⌊A⌋₊/(d^2*e) : ℕ) : ℝ)) else 0)-
        ((B-A)/(e : ℝ))*C)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| *((127/100 : ℝ)*Real.sqrt (B/(e : ℝ))) := by
      apply Finset.sum_le_sum
      intro e he
      have herr := squarefree_coprime_real_rational_interval_floor_error q e A B hq (Nat.pos_of_mem_divisors he) hA hAB hhalf
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Real.sqrt_div hB]
      ring


theorem squarefree_coprime_real_short_interval_euler_error_complete (q : ℕ) (A B : ℝ) (hq : q≠0)
    (hA : 0≤A) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (B-A)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt B*(∏ p ∈ q.primeFactors,(1+1/Real.sqrt (p : ℝ))) := by
  rw [←moebius_half_weighted_divisor_euler_product q hq]
  exact squarefree_coprime_real_short_interval_error q A B hq hA hAB hhalf

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical

theorem solution  (q : ℕ) (A B : ℝ) (hq : q≠0)
    (hA : 0≤A) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (B-A)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt B*(∏ p ∈ q.primeFactors,(1+1/Real.sqrt (p : ℝ))) := Helfgott.squarefree_coprime_real_short_interval_euler_error_complete q A B hq hA hAB hhalf

#print axioms solution
