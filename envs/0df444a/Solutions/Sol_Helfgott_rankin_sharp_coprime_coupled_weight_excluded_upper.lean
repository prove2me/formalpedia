-- Prove2me | solution 1 for Helfgott.rankin_sharp_coprime_coupled_weight_excluded_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:15:20.419989+00:00
-- url     : https://prove2.me/submissions/ae951ff7-c603-4572-881c-1e630554578b

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_Helfgott_rankin_coupled_finite_prime_product_upper

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat
open scoped BigOperators Classical

namespace Helfgott

theorem coprime_moment_reuse_nonnegative_multiplicative_summable_of_local_product_bound
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
set_option Elab.async false
set_option maxHeartbeats 3000000
open Finset Nat
open scoped BigOperators Classical

namespace Helfgott

theorem coprime_moment_reuse_nonnegative_multiplicative_coprime_sum_mul_local_product_le
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
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def coprime_moment_reuse_rankinCoupledMomentWeightSparse (s t : ℝ) (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)^2*(n : ℝ)^(-s-t)/
    (∏ p∈n.primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))

lemma coprime_moment_reuse_rankinCoupledMomentWeightSparse_nonneg (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (n : ℕ) :
    0 ≤ coprime_moment_reuse_rankinCoupledMomentWeightSparse s t n := by
  apply div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hy : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hz : (p : ℝ)^(-t)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hi := Real.rpow_nonneg (Nat.cast_nonneg p) (-1)
  exact mul_nonneg (by linarith) (by linarith)

lemma coprime_moment_reuse_rankinCoupledMomentWeightSparse_mul (s t : ℝ) {m n : ℕ} (hc : Nat.Coprime m n) :
    coprime_moment_reuse_rankinCoupledMomentWeightSparse s t (m*n)=coprime_moment_reuse_rankinCoupledMomentWeightSparse s t m*coprime_moment_reuse_rankinCoupledMomentWeightSparse s t n := by
  have hP : (∏ p∈(m*n).primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))=
      (∏ p∈m.primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))*
      (∏ p∈n.primeFactors,(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))) := by
    rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]
  dsimp [coprime_moment_reuse_rankinCoupledMomentWeightSparse]
  rw [isMultiplicative_moebius.map_mul_of_coprime hc,Int.cast_mul,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity),hP]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_tail (s t : ℝ) (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) :
    coprime_moment_reuse_rankinCoupledMomentWeightSparse s t (p^k)=0 := by
  have hmu : moebius (p^k)=0 := moebius_eq_zero_of_not_squarefree (by
    rw [squarefree_pow_iff hp.ne_one (by omega)]
    simp only [not_and_or]
    exact Or.inr (by omega))
  simp [coprime_moment_reuse_rankinCoupledMomentWeightSparse,hmu]

lemma coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_series (s t : ℝ) (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun k : ℕ => ‖coprime_moment_reuse_rankinCoupledMomentWeightSparse s t (p^k)‖) ∧
      (∑' k : ℕ,coprime_moment_reuse_rankinCoupledMomentWeightSparse s t (p^k))=
        1+(p : ℝ)^(-s-t)/((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))) := by
  constructor
  · apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro k hk
    rw [coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_tail s t p k hp (by simpa only [Finset.mem_range,not_lt] using hk),norm_zero]
  · rw [tsum_eq_sum (s := Finset.range 2) (fun k hk => coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_tail s t p k hp (by simpa only [Finset.mem_range,not_lt] using hk))]
    simp [Finset.sum_range_succ,coprime_moment_reuse_rankinCoupledMomentWeightSparse,hp,moebius_apply_prime hp]

theorem coprime_moment_reuse_rankin_coupled_moment_bound_sparse (s t : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    Summable (coprime_moment_reuse_rankinCoupledMomentWeightSparse s t) ∧
      (∑' n : ℕ,coprime_moment_reuse_rankinCoupledMomentWeightSparse s t n) ≤
        ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
          ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := by
  have hs : 0 < s := by linarith
  have ht : 0 < t := by linarith
  apply coprime_moment_reuse_nonnegative_multiplicative_summable_of_local_product_bound (coprime_moment_reuse_rankinCoupledMomentWeightSparse s t)
    (by simp [coprime_moment_reuse_rankinCoupledMomentWeightSparse]) (by simp [coprime_moment_reuse_rankinCoupledMomentWeightSparse])
    (coprime_moment_reuse_rankinCoupledMomentWeightSparse_nonneg s t hs ht) (fun {_ _} hc => coprime_moment_reuse_rankinCoupledMomentWeightSparse_mul s t hc)
    (fun {p} hp => (coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_series s t p hp).1)
  intro S
  have h := rankin_coupled_finite_prime_product_upper (S.subtype Nat.Prime) s t hs0 hs1 ht0 ht1 hst
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
      exact (coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_series s t p (Finset.mem_filter.mp hp).2).2
    _ ≤ _ := h'

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott
noncomputable def coprime_moment_reuse_rankinSharpCoprimeFactor (q : ℕ) (s : ℝ) : ℝ :=
  ∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-s))
lemma coprime_moment_reuse_mobius_sigma_product_pos (n : ℕ) : (0 : ℝ)<∏ p∈n.primeFactors,((p : ℝ)+1) := by
  apply Finset.prod_pos
  intro p hp
  positivity


lemma coprime_moment_reuse_rankin_sharp_factor_pos (q : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < coprime_moment_reuse_rankinSharpCoprimeFactor q s := by
  unfold coprime_moment_reuse_rankinSharpCoprimeFactor
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hmul := mul_pos (by linarith : (0 : ℝ) < p) (by linarith : 0 < 1-(p : ℝ)^(-s))
  exact div_pos (by linarith) (by nlinarith)

lemma coprime_moment_reuse_rankin_sharp_factor_mul (m n : ℕ) (s : ℝ) (hc : Nat.Coprime m n) :
    coprime_moment_reuse_rankinSharpCoprimeFactor (m*n) s =
      coprime_moment_reuse_rankinSharpCoprimeFactor m s * coprime_moment_reuse_rankinSharpCoprimeFactor n s := by
  unfold coprime_moment_reuse_rankinSharpCoprimeFactor
  rw [hc.primeFactors_mul, Finset.prod_union hc.disjoint_primeFactors]

lemma coprime_moment_reuse_rankin_shifted_local_product_pos (d : ℕ) (s : ℝ) (hs : 0 < s) :
    0 < ∏ p∈d.primeFactors, (1-(p : ℝ)^(-s)+(p : ℝ)^(-1 : ℝ)) := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (p : ℝ)^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hi := Real.rpow_nonneg (Nat.cast_nonneg p) (-1)
  linarith

lemma coprime_moment_reuse_rankin_sharp_factor_squarefree (d : ℕ) (hd : Squarefree d) (s : ℝ) :
    coprime_moment_reuse_rankinSharpCoprimeFactor d s =
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
  unfold coprime_moment_reuse_rankinSharpCoprimeFactor
  rw [Finset.prod_div_distrib, hden]

lemma coprime_moment_reuse_rankin_sharp_coupled_weight_identity (d : ℕ) (hd : 1 ≤ d) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) :
    |((moebius d : ℤ) : ℝ)| / (∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
      (d : ℝ)^(2-s-t) * coprime_moment_reuse_rankinSharpCoprimeFactor d s * coprime_moment_reuse_rankinSharpCoprimeFactor d t =
        coprime_moment_reuse_rankinCoupledMomentWeightSparse s t d := by
  by_cases hsf : Squarefree d
  · have hmuabs : |((moebius d : ℤ) : ℝ)| = 1 := by
      exact_mod_cast abs_moebius_eq_one_of_squarefree hsf
    have hmusq : ((moebius d : ℤ) : ℝ)^2 = 1 := by
      nlinarith [sq_abs (((moebius d : ℤ) : ℝ))]
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd
    have hsp := coprime_moment_reuse_mobius_sigma_product_pos d
    have hbs := coprime_moment_reuse_rankin_shifted_local_product_pos d s hs
    have hbt := coprime_moment_reuse_rankin_shifted_local_product_pos d t ht
    have hpow : (d : ℝ)^(2-s-t) = (d : ℝ)^2*(d : ℝ)^(-s-t) := by
      rw [show 2-s-t = (2 : ℝ)+(-s-t) by ring, Real.rpow_add hdp, Real.rpow_two]
    rw [coprime_moment_reuse_rankin_sharp_factor_squarefree d hsf s, coprime_moment_reuse_rankin_sharp_factor_squarefree d hsf t]
    dsimp [coprime_moment_reuse_rankinCoupledMomentWeightSparse]
    rw [hmuabs, hmusq, hpow, Finset.prod_mul_distrib]
    field_simp [ne_of_gt hdp, ne_of_gt hsp, ne_of_gt hbs, ne_of_gt hbt]
    <;> ring
  · simp [moebius_eq_zero_of_not_squarefree hsf, coprime_moment_reuse_rankinCoupledMomentWeightSparse]


end Helfgott

end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
namespace Helfgott

noncomputable def coprime_moment_reuse_rankinCoupledExcludedProduct (q : ℕ) (s t : ℝ) : ℝ :=
  ∏ p∈q.primeFactors, (1+(p : ℝ)^(-s-t)/
    ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))

lemma coprime_moment_reuse_rankin_coupled_excluded_product_pos (q : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 < coprime_moment_reuse_rankinCoupledExcludedProduct q s t := by
  unfold coprime_moment_reuse_rankinCoupledExcludedProduct
  apply Finset.prod_pos
  intro p hp
  have hfactor : 0 ≤ coprime_moment_reuse_rankinCoupledMomentWeightSparse s t p := coprime_moment_reuse_rankinCoupledMomentWeightSparse_nonneg s t hs ht p
  have hseries := (coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_series s t p (Nat.prime_of_mem_primeFactors hp)).2
  have hsparse : (∑' k : ℕ,coprime_moment_reuse_rankinCoupledMomentWeightSparse s t (p^k))=1+coprime_moment_reuse_rankinCoupledMomentWeightSparse s t p := by
    rw [tsum_eq_sum (s:=Finset.range 2) (fun k hk => coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_tail s t p k
      (Nat.prime_of_mem_primeFactors hp) (by simpa only [Finset.mem_range,not_lt] using hk))]
    simp [Finset.sum_range_succ,coprime_moment_reuse_rankinCoupledMomentWeightSparse]
  rw [←hseries,hsparse]
  linarith

theorem coprime_moment_reuse_rankin_coupled_coprime_moment_upper (q Y : ℕ) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    (∑ n∈Icc 1 Y,if Nat.Coprime n q then coprime_moment_reuse_rankinCoupledMomentWeightSparse s t n else 0) ≤
      (((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
        ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ)))) /
      coprime_moment_reuse_rankinCoupledExcludedProduct q s t := by
  have hs : 0 < s := by linarith
  have ht : 0 < t := by linarith
  apply (le_div_iff₀ (coprime_moment_reuse_rankin_coupled_excluded_product_pos q s t hs ht)).mpr
  have hh := coprime_moment_reuse_nonnegative_multiplicative_coprime_sum_mul_local_product_le
    (coprime_moment_reuse_rankinCoupledMomentWeightSparse s t) (by simp [coprime_moment_reuse_rankinCoupledMomentWeightSparse])
    (coprime_moment_reuse_rankinCoupledMomentWeightSparse_nonneg s t hs ht)
    (fun {_ _} hc => coprime_moment_reuse_rankinCoupledMomentWeightSparse_mul s t hc)
    (fun {p} hp => (coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_series s t p hp).1)
    (((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
      ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ)))) ?_ q Y
  · have heq : (∏ p∈q.primeFactors,∑' k : ℕ,coprime_moment_reuse_rankinCoupledMomentWeightSparse s t (p^k))=
        coprime_moment_reuse_rankinCoupledExcludedProduct q s t := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_series s t p (Nat.prime_of_mem_primeFactors hp)).2
    rwa [heq] at hh
  · intro S
    have h := rankin_coupled_finite_prime_product_upper (S.subtype Nat.Prime) s t hs0 hs1 ht0 ht1 hst
    have h' : (∏ p∈S with Nat.Prime p,(1+(p : ℝ)^(-s-t)/
        ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))) ≤
        ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
          ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := by
      exact (Finset.prod_subtype_eq_prod_filter (s:=S) (p:=Nat.Prime) (fun p : ℕ =>
        (1+(p : ℝ)^(-s-t)/((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))))).symm.trans_le h
    apply le_trans _ h'
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro p hp
    exact (coprime_moment_reuse_rankinCoupledMomentWeightSparse_prime_series s t p (Finset.mem_filter.mp hp).2).2

theorem rankin_sharp_coprime_coupled_weight_excluded_upper_complete (q D : ℕ) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    let J : ℕ → ℝ → ℝ := fun n u =>
      ∏ p∈n.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u))
    let H : ℝ := ∏ p∈q.primeFactors,(1+(p : ℝ)^(-s-t)/
      ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))
    (∑ d∈Icc 1 D,if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2*
        (d : ℝ)^(2-s-t)*J (d*q) s*J (d*q) t else 0) ≤
      J q s*J q t *
        ((((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
          ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))))/H) := by
  have hs : 0 < s := by linarith
  have ht : 0 < t := by linarith
  dsimp only
  change (∑ d∈Icc 1 D,if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2*
        (d : ℝ)^(2-s-t)*coprime_moment_reuse_rankinSharpCoprimeFactor (d*q) s*coprime_moment_reuse_rankinSharpCoprimeFactor (d*q) t else 0) ≤ _
  have heq : (∑ d∈Icc 1 D,if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2*
        (d : ℝ)^(2-s-t)*coprime_moment_reuse_rankinSharpCoprimeFactor (d*q) s*coprime_moment_reuse_rankinSharpCoprimeFactor (d*q) t else 0) =
      (coprime_moment_reuse_rankinSharpCoprimeFactor q s*coprime_moment_reuse_rankinSharpCoprimeFactor q t)*
        (∑ d∈Icc 1 D,if Nat.Coprime d q then coprime_moment_reuse_rankinCoupledMomentWeightSparse s t d else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hdI
    by_cases hc : Nat.Coprime d q
    · simp only [if_pos hc]
      rw [coprime_moment_reuse_rankin_sharp_factor_mul d q s hc,coprime_moment_reuse_rankin_sharp_factor_mul d q t hc,
        ←coprime_moment_reuse_rankin_sharp_coupled_weight_identity d (Finset.mem_Icc.mp hdI).1 s t hs ht]
      ring
    · simp only [if_neg hc,mul_zero]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (coprime_moment_reuse_rankin_coupled_coprime_moment_upper q D s t hs0 hs1 ht0 ht1 hst)
    (mul_nonneg (coprime_moment_reuse_rankin_sharp_factor_pos q s hs).le (coprime_moment_reuse_rankin_sharp_factor_pos q t ht).le)
end Helfgott
end

open Helfgott Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical
theorem solution  (q D : ℕ) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    let J : ℕ → ℝ → ℝ := fun n u =>
      ∏ p∈n.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u))
    let H : ℝ := ∏ p∈q.primeFactors,(1+(p : ℝ)^(-s-t)/
      ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))
    (∑ d∈Icc 1 D,if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2*
        (d : ℝ)^(2-s-t)*J (d*q) s*J (d*q) t else 0) ≤
      J q s*J q t *
        ((((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
          ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))))/H) := Helfgott.rankin_sharp_coprime_coupled_weight_excluded_upper_complete q D s t hs0 hs1 ht0 ht1 hst
#print axioms solution
