-- Prove2me | solution 1 for GlobalTheory.cell_columns_saturated_and_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:07.640593+00:00
-- url     : https://prove2.me/submissions/5b5aac90-e739-454d-b8ed-b294b42932f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsTriangularOfSpanFirstColumnsLe
import Theorems.Thm_GlobalTheory_mem_span_first_columns_iff
import Theorems.Thm_GlobalTheory_exists_triangular_of_span_first_columns_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V L : Type) [CommRing V] [IsDomain V] [Field L] [Algebra V L] [IsFractionRing V L] (n r : ℕ) (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) → (∀ (k : ℕ) (x : Fin n → V), (fun i => algebraMap V L (x i)) ∈ Submodule.span L {y : Fin n → L | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => algebraMap V L (u i j)} ↔ x ∈ Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) ∧ ∀ u' : Matrix (Fin n) (Fin r) V, (∀ k : ℕ, Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u' i j} = Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) → ∃ b : Matrix (Fin r) (Fin r) V, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ u' = u * b := by
  intro V L _ _ _ _ _ n r ι u ⟨h0, h1⟩
  set A : Matrix (Fin r) (Fin r) V := u.submatrix ι id with hA
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_lowerTriangular A (fun i j hij => h0 i j hij)]
    simp [hA, h1]
  have hAu : IsUnit A.det := hdet ▸ isUnit_one
  have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
  have hmap : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin r) V) (c : Fin r → V) (i : Fin m),
      algebraMap V L ((M *ᵥ c) i) =
        ((M.map (algebraMap V L)) *ᵥ (fun j => algebraMap V L (c j))) i := by
    intro m M c i
    simp [Matrix.mulVec, dotProduct]
  refine ⟨fun k x => ?_, fun u' hu' => ?_⟩
  · have e := mem_span_first_columns_iff (u.map (algebraMap V L)) k
      (fun i => algebraMap V L (x i))
    simp only [Matrix.map_apply] at e
    rw [e, mem_span_first_columns_iff]
    constructor
    · rintro ⟨c, hc, hx⟩
      set c₀ : Fin r → V := A⁻¹ *ᵥ (fun i => x (ι i)) with hc₀
      have hAc : A *ᵥ c₀ = fun i => x (ι i) := by
        rw [hc₀, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
      have hAL : IsUnit (A.map (algebraMap V L)) := by
        rw [Matrix.isUnit_iff_isUnit_det]
        have := (algebraMap V L).map_det A
        rw [hdet, map_one] at this
        exact (show (1 : L) = (A.map (algebraMap V L)).det from this) ▸ isUnit_one
      have hcc : (fun j => algebraMap V L (c₀ j)) = c := by
        apply Matrix.mulVec_injective_iff_isUnit.mpr hAL
        ext i
        rw [← hmap, hAc]
        exact congrFun hx (ι i)
      refine ⟨c₀, fun j hj => hinj ?_, ?_⟩
      · rw [map_zero, ← hc j hj, ← hcc]
      · ext i
        apply hinj
        rw [hmap, hcc]
        exact congrFun hx i
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun j => algebraMap V L (c j), fun j hj => by simp [hc j hj], ?_⟩
      ext i
      exact hmap u c i
  · obtain ⟨b, hb, hub⟩ := exists_triangular_of_span_first_columns_le u u' fun k => (hu' k).le
    obtain ⟨b', hb', hub'⟩ := exists_triangular_of_span_first_columns_le u' u fun k => (hu' k).ge
    have h2 : u = u * (b * b') := by rw [← Matrix.mul_assoc, ← hub, ← hub']
    have h3 : A = A * (b * b') := by
      ext i j
      exact congrFun (congrFun h2 (ι i)) j
    have h4 : b * b' = 1 := by
      have := congrArg (fun M => A⁻¹ * M) h3
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mul] at this
      exact this.symm
    refine ⟨b, hb, fun i => ?_, hub⟩
    have h5 : (b * b') i i = b i i * b' i i := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hb h, zero_mul]
      · rw [hb' h, mul_zero]
    rw [h4, Matrix.one_apply_eq] at h5
    exact IsUnit.of_mul_eq_one _ h5.symm
end GlobalTheory
