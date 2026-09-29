-- Prove2me | solution 1 for ModularCurve.MultCovering.compConst_eq_of_t_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/bf25a41b-5a24-553a-a308-871a8f330d48

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_compConst_eq_of_t_eq_sum

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution (p : ℕ) [Fact p.Prime] {r : ℕ} (Φ Φ' : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (U : Matrix (Fin r) (Fin r) ℚ) (hUunit : IsUnit U)
    (hU : ∀ i j, 0 ≤ padicValRat p (U i j) ∨ U i j = 0)
    (hUinv : ∀ i j, 0 ≤ padicValRat p (U⁻¹ i j) ∨ U⁻¹ i j = 0)
    (ht : ∀ i, Φ'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j) :
    compConst Φ' s hs = compConst Φ s hs := by
  have hp : p.Prime := Fact.out

  set Ub : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) := (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix U with hUb
  set Ubi : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) := (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix U⁻¹ with hUbi
  have hdetU : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).1 hUunit
  have hUU1 : Ubi * Ub = 1 := by rw [hUb, hUbi, ← map_mul, Matrix.nonsing_inv_mul U hdetU, map_one]
  have hUU2 : Ub * Ubi = 1 := by rw [hUb, hUbi, ← map_mul, Matrix.mul_nonsing_inv U hdetU, map_one]
  have pint_mem : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p → ∀ q : ℚ,
      (0 ≤ padicValRat p q ∨ q = 0) → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A := by
    intro A hA q hq
    rw [eq_ratCast]
    rcases eq_or_ne q 0 with rfl | hq0
    · simp
    rcases hq with h | h
    · have hAp : A.valuation (p : (AlgebraicClosure ℚ)) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
      exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hq0).2 h
    · exact absurd h hq0
  have hUbA : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p → ∀ i j, Ub i j ∈ A ∧ Ubi i j ∈ A :=
    fun A hA i j => ⟨pint_mem A hA _ (hU i j), pint_mem A hA _ (hUinv i j)⟩

  have ht1 : ∀ i, Φ'.t i = ∑ j, Ub i j • Φ.t j := by
    intro i; rw [ht i]
    exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def]; rfl
  have ht2 : ∀ j, Φ.t j = ∑ i, Ubi j i • Φ'.t i := by
    intro j
    simp_rw [ht1, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ k, (∑ i, Ubi j i * Ub i k) • Φ.t k = (if j = k then (1 : (AlgebraicClosure ℚ)) else 0) • Φ.t k := by
      intro k
      have h1 := congrFun (congrFun hUU1 j) k
      simp only [Matrix.mul_apply, Matrix.one_apply] at h1
      rw [h1]
    simp_rw [← Finset.sum_smul, this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  have coord : ∀ {v : Fin r → ↥(modularFunctionFieldBar (1 * p))} (hv : LinearIndependent (AlgebraicClosure ℚ) v) (c : Fin r → (AlgebraicClosure ℚ))
      (x : ↥(modularFunctionFieldBar (1 * p))) (hx : x ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range v)) (heq : x = ∑ k, c k • v k) (k : Fin r),
      hv.repr ⟨x, hx⟩ k = c k := by
    intro v hv c x hx heq k
    have h1 := hv.linearCombination_repr ⟨x, hx⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by exact zero_smul _ _)] at h1
    have h2 : ∑ i, (hv.repr ⟨x, hx⟩ i - c i) • v i = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, ← heq]; exact h1
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv _ h2 k)

  have hs_t : ∀ i, s i = ∑ j, linkMatrix Φ s hs i j • Φ.t j := by
    intro i
    have h1 := Φ.t_basis.1.linearCombination_repr ⟨s i, mem_span_range_goodFamily Φ s hs i⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by exact zero_smul _ _)] at h1
    exact h1.symm
  have ht_s : ∀ i, Φ.t i = ∑ j, linkMatrixInv Φ s hs i j • s j := by
    intro i
    have h1 := hs.1.linearCombination_repr ⟨Φ.t i, goodFamily_mem_span_range Φ s hs i⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by exact zero_smul _ _)] at h1
    exact h1.symm
  have hM' : ∀ i k, linkMatrix Φ' s hs i k = ∑ j, linkMatrix Φ s hs i j * Ubi j k := by
    intro i k
    rw [linkMatrix_apply]
    apply coord Φ'.t_basis.1 (fun k => ∑ j, linkMatrix Φ s hs i j * Ubi j k) (s i)
    rw [hs_t i]
    simp_rw [ht2, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hMinv' : ∀ i k, linkMatrixInv Φ' s hs i k = ∑ j, Ub i j * linkMatrixInv Φ s hs j k := by
    intro i k
    rw [linkMatrixInv_apply]
    apply coord hs.1 (fun k => ∑ j, Ub i j * linkMatrixInv Φ s hs j k) (Φ'.t i)
    rw [ht1 i]
    simp_rw [ht_s, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

  have hM : ∀ i k, linkMatrix Φ s hs i k = ∑ j, linkMatrix Φ' s hs i j * Ub j k := by
    intro i k
    simp_rw [hM', Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ x, linkMatrix Φ s hs i j * (Ubi j x * Ub x k) = linkMatrix Φ s hs i j * (if j = k then 1 else 0) := by
      intro j; rw [← Finset.mul_sum]; congr 1
      have h1 := congrFun (congrFun hUU1 j) k
      simp only [Matrix.mul_apply, Matrix.one_apply] at h1; exact h1
    simp_rw [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hMinv : ∀ i k, linkMatrixInv Φ s hs i k = ∑ j, Ubi i j * linkMatrixInv Φ' s hs j k := by
    intro i k
    simp_rw [hMinv', Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ x, Ubi i x * Ub x j * linkMatrixInv Φ s hs j k = (if i = j then 1 else 0) * linkMatrixInv Φ s hs j k := by
      intro j; rw [← Finset.sum_mul]; congr 1
      have h1 := congrFun (congrFun hUU1 i) j
      simp only [Matrix.mul_apply, Matrix.one_apply] at h1; exact h1
    simp_rw [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  have hset : {B : ℕ | ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ i j, (p : (AlgebraicClosure ℚ)) ^ B * linkMatrix Φ' s hs i j ∈ A ∧ (p : (AlgebraicClosure ℚ)) ^ B * linkMatrixInv Φ' s hs i j ∈ A}
      = {B : ℕ | ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ i j, (p : (AlgebraicClosure ℚ)) ^ B * linkMatrix Φ s hs i j ∈ A ∧ (p : (AlgebraicClosure ℚ)) ^ B * linkMatrixInv Φ s hs i j ∈ A} := by
    ext B
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h A hA i j
      constructor
      · rw [hM i j, Finset.mul_sum]
        exact sum_mem fun k _ => by rw [← mul_assoc]; exact mul_mem (h A hA i k).1 (hUbA A hA k j).1
      · rw [hMinv i j, Finset.mul_sum]
        exact sum_mem fun k _ => by rw [mul_left_comm]; exact mul_mem (hUbA A hA i k).2 (h A hA k j).2
    · intro h A hA i j
      constructor
      · rw [hM' i j, Finset.mul_sum]
        exact sum_mem fun k _ => by rw [← mul_assoc]; exact mul_mem (h A hA i k).1 (hUbA A hA k j).2
      · rw [hMinv' i j, Finset.mul_sum]
        exact sum_mem fun k _ => by rw [mul_left_comm]; exact mul_mem (hUbA A hA i k).1 (h A hA k j).2
  have hbud : linkBudget Φ' s hs = linkBudget Φ s hs := by
    unfold linkBudget; rw [hset]
  rw [compConst_eq, compConst_eq, hbud]

end S_ModularCurve_MultCovering_compConst_eq_of_t_eq_sum
end P2MW
export P2MW.S_ModularCurve_MultCovering_compConst_eq_of_t_eq_sum (solution)
