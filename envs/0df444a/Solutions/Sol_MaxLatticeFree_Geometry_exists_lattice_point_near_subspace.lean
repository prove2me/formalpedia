-- Prove2me | solution 1 for MaxLatticeFree.Geometry.exists_lattice_point_near_subspace
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:49:38.011778+00:00
-- url     : https://prove2.me/submissions/e4606e42-b177-48d9-8ea1-98d7d3dc03df

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Theorems.Thm_MaxLatticeFree_Geometry_exists_lattice_point_near_halfLine

namespace MaxLatticeFree.Geometry.NearSubspaceProof

open Module
set_option maxHeartbeats 800000

lemma lambdaSubspace_of_span {n : ℕ}
    (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hLV : L ≤ V)
    (hspan : Submodule.span ℝ ((Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ L) = L) :
    IsLambdaSubspace Λ V L := by
  classical
  let T : Set (EuclideanSpace ℝ (Fin n)) := (Λ : Set _) ∩ L
  let hs := linearIndepOn_empty ℝ (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  let B := hs.extend (Set.empty_subset T)
  have hB : LinearIndependent ℝ (fun b : B => (b : EuclideanSpace ℝ (Fin n))) :=
    (hs.linearIndepOn_extend (Set.empty_subset T)).linearIndependent_restrict
  let : Finite B := hB.finite
  let : Fintype B := Fintype.ofFinite B
  let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  let b : Fin (Fintype.card B) → EuclideanSpace ℝ (Fin n) := fun i => e i
  have hrange : Set.range b = B := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x,hx⟩, by simp [b]⟩
  refine ⟨hLV,Fintype.card B,b,hB.comp e e.injective,?_,?_⟩
  · rw [hrange, ← hspan]
    apply le_antisymm
    · exact Submodule.span_mono (hs.extend_subset (Set.empty_subset T))
    · exact Submodule.span_le.mpr (hs.subset_span_extend (Set.empty_subset T))
  · intro i
    exact (hs.extend_subset (Set.empty_subset T) (e i).property).1

end MaxLatticeFree.Geometry.NearSubspaceProof

open MaxLatticeFree.Geometry

theorem solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hLV : L ≤ V) (hL : ¬ IsLambdaSubspace Λ V L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ Λ, y ∉ L ∧ Metric.infDist y (L : Set (EuclideanSpace ℝ (Fin n))) < ε := by
  classical
  let K := Submodule.span ℝ ((Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ L)
  have hKL : K ≤ L := Submodule.span_le.mpr fun _ hx => hx.2
  have hne : K ≠ L := by
    intro he
    exact hL (NearSubspaceProof.lambdaSubspace_of_span Λ V L hLV he)
  have horth : Kᗮ ⊓ L ≠ ⊥ := by
    intro he
    have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKL
    rw [he, sup_bot_eq] at h
    exact hne h
  obtain ⟨r,hr,hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  have hrnorm : 0 < ‖r‖ := norm_pos_iff.mpr hr0
  have hlam : 0 ≤ ε / ‖r‖ := le_of_lt (div_pos hε hrnorm)
  obtain ⟨y,hy,_hne,hnear⟩ := exists_lattice_point_near_halfLine Λ V hΛ 0 Λ.zero_mem
    r (hLV hr.2) hr0 ε hε (ε / ‖r‖) hlam
  have hray : ({p : EuclideanSpace ℝ (Fin n) |
      ∃ t : ℝ, ε / ‖r‖ ≤ t ∧ p = 0 + t • r} : Set _).Nonempty :=
    ⟨(ε / ‖r‖) • r, ε / ‖r‖, le_rfl, by simp⟩
  obtain ⟨p,⟨t,ht,rfl⟩,hpoint⟩ := (Metric.infDist_lt_iff hray).mp hnear
  simp only [zero_add] at hpoint
  refine ⟨y,hy,?_,(Metric.infDist_le_dist_of_mem (L.smul_mem t hr.2)).trans_lt hpoint⟩
  intro hyL
  have hyK : y ∈ K := Submodule.subset_span ⟨hy,hyL⟩
  have hi : inner ℝ y (t • r) = 0 := by
    rw [real_inner_smul_right, Submodule.inner_right_of_mem_orthogonal hyK hr.1, mul_zero]
  have hpyth := norm_sub_sq_eq_norm_sq_add_norm_sq_real hi
  have hle : ‖t • r‖ ≤ ‖y - t • r‖ := by
    nlinarith [norm_nonneg (t • r), norm_nonneg (y - t • r), sq_nonneg ‖y‖]
  have hlarge : ε ≤ ‖t • r‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hlam.trans ht)]
    exact (div_le_iff₀ hrnorm).mp ht
  have hsmall : ‖y - t • r‖ < ε := by simpa only [dist_eq_norm] using hpoint
  exact (not_lt_of_ge (hlarge.trans hle)) hsmall
