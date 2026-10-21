-- Prove2me | solution 1 for LowRankMarkov.RankMLE.rank_remark_nuclear_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:32:22.624549+00:00
-- url     : https://prove2.me/submissions/9bc2182c-c465-407e-9dff-07983d469c70

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

open CaiCandesShen.Convergence Module

namespace LRMNucAux

theorem rank_sub_le' {p : ℕ} (A B : Matrix (Fin p) (Fin p) ℝ) :
    (A - B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rintro y ⟨x, rfl⟩
  rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec]
  exact Submodule.sub_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

theorem finrank_range_toEuclideanLin {p : ℕ} (X : Matrix (Fin p) (Fin p) ℝ) :
    finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X)) = X.rank := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin]

theorem trace_adj_comp_self {p : ℕ} (X : Matrix (Fin p) (Fin p) ℝ) :
    ((Matrix.toEuclideanLin X).adjoint ∘ₗ Matrix.toEuclideanLin X).trace ℝ _ =
      ∑ i, ∑ j, X i j * X i j := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin p) ℝ)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

theorem nuclear_le {p : ℕ} (X : Matrix (Fin p) (Fin p) ℝ) :
    nuclearNorm X ≤ Real.sqrt (X.rank : ℝ) * frobNorm X := by
  set T := Matrix.toEuclideanLin X
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin p)) = p := finrank_euclideanSpace_fin
  have hsupp := T.support_singularValues
  have hk : finrank ℝ (LinearMap.range T) = X.rank := finrank_range_toEuclideanLin X
  rw [hk] at hsupp
  have hnuc : nuclearNorm X = ∑ i ∈ Finset.range X.rank, T.singularValues i := by
    unfold nuclearNorm; rw [Finsupp.sum, hsupp]
  have hkp : X.rank ≤ p := Matrix.rank_le_width X
  have hsq : ∑ i ∈ Finset.range X.rank, T.singularValues i ^ 2 = frobInner X X := by
    have h1 : ∑ i ∈ Finset.range X.rank, T.singularValues i ^ 2 =
        ∑ i ∈ Finset.range p, T.singularValues i ^ 2 := by
      apply Finset.sum_subset (Finset.range_subset_range.2 hkp)
      intro i _ hi
      have : T.singularValues i = 0 := by
        by_contra hne
        have : i ∈ T.singularValues.support := Finsupp.mem_support_iff.2 hne
        rw [hsupp] at this; exact hi this
      simp [this]
    rw [h1, Finset.sum_range (fun i => T.singularValues i ^ 2)]
    have h2 : ∀ i : Fin p, T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hfin i :=
      fun i => T.sq_singularValues_fin hfin i
    simp_rw [h2]
    rw [← T.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues hfin]
    simp only [RCLike.re_to_real]
    rw [trace_adj_comp_self]; rfl
  have hnn : 0 ≤ nuclearNorm X := by
    rw [hnuc]; exact Finset.sum_nonneg fun i _ => T.singularValues_nonneg i
  have hF : 0 ≤ frobInner X X := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.range X.rank) (f := fun i => T.singularValues i)
  rw [Finset.card_range, hsq, ← hnuc] at hCS
  unfold frobNorm
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.le_sqrt_of_sq_le hCS

end LRMNucAux

open LRMNucAux in
theorem solution {p r : ℕ} (P Q : Matrix (Fin p) (Fin p) ℝ)
    (hP : P.rank = r) (hQ : Q.rank ≤ r) :
    (Q - P).rank ≤ 2 * r ∧
      nuclearNorm (Q - P) ≤ Real.sqrt (2 * (r : ℝ)) * frobNorm (Q - P) := by
  have hr : (Q - P).rank ≤ 2 * r := by
    have := rank_sub_le' Q P; omega
  refine ⟨hr, le_trans (nuclear_le _) ?_⟩
  have hF : 0 ≤ frobNorm (Q - P) := Real.sqrt_nonneg _
  apply mul_le_mul_of_nonneg_right _ hF
  apply Real.sqrt_le_sqrt
  exact_mod_cast hr
