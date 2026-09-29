-- Prove2me | solution 1 for LassoDantzig.REConditions.eq_A1_projection_triangle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:53:20.830251+00:00
-- url     : https://prove2.me/submissions/e750115a-5ef3-4208-a0a7-e9006efc6f1e

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

theorem aux_a1pt_decomp {M : ℕ} (δ : Fin M → ℝ) (J0 : Finset (Fin M))
    (J : ℕ → Finset (Fin M)) (K : ℕ) (hJ : IsBlockPartition J0ᶜ J K) :
    δ = restrict δ (J0 ∪ J 1) + ∑ k ∈ Finset.Icc 2 K, restrict δ (J k) := by
  obtain ⟨hK, hdisj, hU⟩ := hJ
  funext j
  simp only [Pi.add_apply, Finset.sum_apply, restrict]
  by_cases hS : j ∈ J0 ∪ J 1
  · rw [if_pos hS]
    have hno : ∀ k ∈ Finset.Icc 2 K, j ∉ J k := by
      intro k hk hjk
      have hk' := Finset.mem_Icc.1 hk
      rcases Finset.mem_union.1 hS with h0 | h1
      · have hmem : j ∈ (Finset.Icc 1 K).biUnion J :=
          Finset.mem_biUnion.2 ⟨k, Finset.mem_Icc.2 ⟨by omega, hk'.2⟩, hjk⟩
        rw [hU] at hmem
        exact (Finset.mem_compl.1 hmem) h0
      · exact Finset.disjoint_left.1
          (hdisj 1 (Finset.mem_Icc.2 ⟨le_refl 1, hK⟩) k (Finset.mem_Icc.2 ⟨by omega, hk'.2⟩)
            (by omega)) h1 hjk
    rw [Finset.sum_eq_zero (fun k hk => if_neg (hno k hk))]
    simp
  · rw [if_neg hS, zero_add]
    have hj0 : j ∉ J0 := fun h => hS (Finset.mem_union_left _ h)
    have hj1 : j ∉ J 1 := fun h => hS (Finset.mem_union_right _ h)
    have hc : j ∈ (Finset.Icc 1 K).biUnion J := by
      rw [hU]; exact Finset.mem_compl.2 hj0
    obtain ⟨k0, hk0, hjk0⟩ := Finset.mem_biUnion.1 hc
    have hk0'' := Finset.mem_Icc.1 hk0
    have hk01 : k0 ≠ 1 := by
      rintro rfl; exact hj1 hjk0
    have hk0' : k0 ∈ Finset.Icc 2 K := Finset.mem_Icc.2 ⟨by omega, hk0''.2⟩
    rw [Finset.sum_eq_single k0]
    · rw [if_pos hjk0]
    · intro b hb hne
      have hb' := Finset.mem_Icc.1 hb
      rw [if_neg]
      intro hjb
      exact Finset.disjoint_left.1
        (hdisj b (Finset.mem_Icc.2 ⟨by omega, hb'.2⟩) k0 hk0 hne) hjb hjk0
    · intro h; exact absurd hk0' h

theorem aux_a1pt_mulVec_restrict {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (δ : Fin M → ℝ) (S : Finset (Fin M)) :
    X.mulVec (restrict δ S) = ∑ j ∈ S, δ j • (fun i => X i j) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, restrict, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem aux_a1pt_mem {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (δ : Fin M → ℝ) (S : Finset (Fin M)) :
    WithLp.toLp 2 (X.mulVec (restrict δ S)) ∈ colSpan X S := by
  rw [aux_a1pt_mulVec_restrict, WithLp.toLp_sum]
  refine Submodule.sum_mem _ (fun j hj => ?_)
  rw [WithLp.toLp_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

theorem aux_a1pt_norm {n : ℕ} (w : Fin n → ℝ) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n))‖ = euclNorm w := by
  rw [EuclideanSpace.norm_eq, euclNorm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

end LassoDantzig.REConditions

open LassoDantzig.REConditions

theorem solution {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (δ : Fin M → ℝ) (J0 : Finset (Fin M)) (J : ℕ → Finset (Fin M)) (K : ℕ)
    (hJ : IsBlockPartition J0ᶜ J K) :
    projNorm X (J0 ∪ J 1) (X.mulVec (restrict δ (J0 ∪ J 1))) -
        ‖∑ k ∈ Finset.Icc 2 K,
          (colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J k))))‖
      ≤ projNorm X (J0 ∪ J 1) (X.mulVec δ) ∧
    projNorm X (J0 ∪ J 1) (X.mulVec (restrict δ (J0 ∪ J 1))) =
      euclNorm (X.mulVec (restrict δ (J0 ∪ J 1))) ∧
    euclNorm (X.mulVec (restrict δ (J0 ∪ J 1))) -
        ∑ k ∈ Finset.Icc 2 K, projNorm X (J0 ∪ J 1) (X.mulVec (restrict δ (J k)))
      ≤ euclNorm (X.mulVec (restrict δ (J0 ∪ J 1))) -
        ‖∑ k ∈ Finset.Icc 2 K,
          (colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J k))))‖ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold projNorm
    have hd := aux_a1pt_decomp δ J0 J K hJ
    have hX : X.mulVec δ = X.mulVec (restrict δ (J0 ∪ J 1)) +
        ∑ k ∈ Finset.Icc 2 K, X.mulVec (restrict δ (J k)) := by
      conv_lhs => rw [hd]
      rw [Matrix.mulVec_add, Matrix.mulVec_sum]
    rw [hX, WithLp.toLp_add, WithLp.toLp_sum, map_add, map_sum]
    have h := norm_sub_le
      ((colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J0 ∪ J 1))))
        + ∑ k ∈ Finset.Icc 2 K,
          (colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J k)))))
      (∑ k ∈ Finset.Icc 2 K,
          (colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J k)))))
    rw [add_sub_cancel_right] at h
    linarith
  · unfold projNorm
    rw [Submodule.starProjection_eq_self_iff.2 (aux_a1pt_mem X δ (J0 ∪ J 1)), aux_a1pt_norm]
  · unfold projNorm
    have := norm_sum_le (Finset.Icc 2 K) (fun k =>
      (colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J k)))))
    linarith
