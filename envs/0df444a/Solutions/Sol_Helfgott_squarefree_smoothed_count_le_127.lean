-- Prove2me | solution 1 for Helfgott.squarefree_smoothed_count_le_127
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T14:40:16.741741+00:00
-- url     : https://prove2.me/submissions/740557a7-605a-450c-8b99-888a04bbc870

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

theorem squarefree_smoothed_count_le_127_complete (x : ℝ) (hx : 0≤x) :
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

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical

theorem solution  (x : ℝ) (hx : 0≤x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,((moebius n : ℤ) : ℝ)^2)+
    (x^2/2)*(∑' n : ℕ,if ⌊x⌋₊<n then ((moebius n : ℤ) : ℝ)^2/(n : ℝ)^2 else 0)≤(127/100 : ℝ)*x := Helfgott.squarefree_smoothed_count_le_127_complete x hx

#print axioms solution
