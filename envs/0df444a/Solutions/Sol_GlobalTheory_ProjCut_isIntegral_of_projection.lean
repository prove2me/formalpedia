-- Prove2me | solution 1 for GlobalTheory.ProjCut.isIntegral_of_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:51.661454+00:00
-- url     : https://prove2.me/submissions/0126040d-b9ed-42e7-8b2c-8ea4ed5dcb74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_prod_pow_natDegree_coeff__4e974f93833c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module
open GlobalTheory
open GlobalTheory.ProjCut
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
open ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
variable {ι k : Type*} [Field k]
namespace GlobalTheory.ProjCut
theorem _root_.solution {σ R A : Type*} [Fintype σ] [CommRing R] [Algebra k R]
    [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    (w : σ → A) (a : σ → R) (c : σ → k) (t : A)
    (h : ∀ j, w j = algebraMap k A (c j) * t + algebraMap R A (a j))
    {g : MvPolynomial σ k} {m : ℕ} (hg : g.IsHomogeneous m) (hw : aeval w g = 0)
    (hc : eval c g ≠ 0)
    (hint : (aeval w : MvPolynomial σ k →ₐ[k] A).toRingHom.IsIntegral) :
    Algebra.IsIntegral R A := by
  classical
  let v : σ → Polynomial R := fun j =>
    Polynomial.C (algebraMap k R (c j)) * Polynomial.X + Polynomial.C (a j)
  let Q : Polynomial R := aeval v g
  have hv : ∀ i, (v i).natDegree ≤ 1 := fun i => Polynomial.natDegree_linear_le
  have hv1 : ∀ i, (v i).coeff 1 = algebraMap k R (c i) := by
    intro i
    simp [v, Polynomial.coeff_C]
  have hQe : Q = ∑ d ∈ g.support,
      Polynomial.C (algebraMap k R (g.coeff d)) * ∏ i, v i ^ d i := by
    simp only [Q, aeval_def, eval₂_eq']
    rfl
  have hdeg : ∀ d ∈ g.support, ∑ i, d i = m := by
    intro d hd
    have := hg (mem_support_iff.mp hd)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  have hQ1 : Q.natDegree ≤ m := by
    rw [hQe]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [← hdeg d hd]
    exact (prod_pow_natDegree_coeff' Finset.univ v d hv).1
  have hQ2 : Q.coeff m = algebraMap k R (eval c g) := by
    rw [hQe, Polynomial.finsetSum_coeff, eval_eq', map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Polynomial.coeff_C_mul, ← hdeg d hd, (prod_pow_natDegree_coeff' Finset.univ v d hv).2]
    simp [hv1]
  have hQ3 : Polynomial.aeval t Q = 0 := by
    have := comp_aeval_apply v ((Polynomial.aeval t : Polynomial R →ₐ[R] A).restrictScalars k) g
    simp only [AlgHom.restrictScalars_apply] at this
    rw [← hw, this]
    congr 2
    funext j
    simp [v, h j, ← IsScalarTower.algebraMap_apply]
  have ht : IsIntegral R t := by
    refine ⟨Polynomial.C (algebraMap k R (eval c g)⁻¹) * Q, ?_, ?_⟩
    · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one m
        ((Polynomial.natDegree_C_mul_le _ _).trans hQ1) ?_
      rw [Polynomial.coeff_C_mul, hQ2, ← map_mul, inv_mul_cancel₀ hc, map_one]
    · rw [← Polynomial.aeval_def, map_mul, hQ3, mul_zero]
  let B := integralClosure R A
  have hk : ∀ x : k, algebraMap k A x ∈ B := fun x => by
    rw [IsScalarTower.algebraMap_apply k R A]; exact B.algebraMap_mem _
  have hB : ∀ p : MvPolynomial σ k, (aeval w : MvPolynomial σ k →ₐ[k] A).toRingHom p ∈ B := by
    intro p
    change aeval w p ∈ B
    induction p using MvPolynomial.induction_on with
    | C x => rw [algHom_C]; exact hk x
    | add p q hp hq => rw [map_add]; exact B.add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, aeval_X, h]
      exact B.mul_mem hp (B.add_mem (B.mul_mem (hk _) ht) (B.algebraMap_mem _))
  have hB' : (algebraMap B A).IsIntegral :=
    RingHom.IsIntegral.tower_top
      ((aeval w : MvPolynomial σ k →ₐ[k] A).toRingHom.codRestrict B hB) (algebraMap B A) hint
  exact ⟨fun x => isIntegral_trans (A := B) x (hB' x)⟩
end GlobalTheory.ProjCut
