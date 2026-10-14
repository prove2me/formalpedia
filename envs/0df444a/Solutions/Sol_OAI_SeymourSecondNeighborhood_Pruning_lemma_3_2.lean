-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T20:32:11.665146+00:00
-- url     : https://prove2.me/submissions/e192bfdd-5d0a-4e07-ae24-08eb3073b7e5

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

set_option autoImplicit false
open Finset

namespace OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_2

/-- The elementary matrix with a single `1` at position `(s, j)`. -/
def unitMat {I J : Type*} [DecidableEq I] [DecidableEq J] (s : I) (j : J) : Matrix I J ℝ :=
  Matrix.of fun a b => (Pi.single s (1 : ℝ) : I → ℝ) a * (Pi.single j (1 : ℝ) : J → ℝ) b

theorem unitMat_apply_of_not_mem {I J : Type*} [DecidableEq I] [DecidableEq J]
    (T : Finset (I × J)) (s : I) (j : J) (hsj : (s, j) ∈ T) (a : I) (b : J)
    (hab : (a, b) ∉ T) : unitMat s j a b = 0 := by
  simp only [unitMat, Matrix.of_apply]
  by_cases ha : a = s
  · by_cases hb : b = j
    · subst ha; subst hb; exact absurd hsj hab
    · rw [Pi.single_eq_of_ne hb, mul_zero]
  · rw [Pi.single_eq_of_ne ha, zero_mul]

theorem unitMat_mulVec {I J : Type*} [Fintype J] [DecidableEq I] [DecidableEq J]
    (s : I) (j : J) (w : J → ℝ) :
    (unitMat s j).mulVec w = (w j) • Pi.single s (1 : ℝ) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, unitMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    mul_assoc]
  rw [← Finset.mul_sum]
  have h := single_dotProduct (v := w) (1 : ℝ) j
  simp only [dotProduct] at h
  rw [h, one_mul, mul_comm]

theorem range_lt {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (D : Matrix I J ℝ) (s : I) (j : J) (x : J → ℝ) (hx : D.mulVec x = 0) (hxj : x j ≠ 0)
    (y : I → ℝ) (hy : D.transpose.mulVec y = 0) (hys : y s ≠ 0) :
    LinearMap.range D.mulVecLin < LinearMap.range (D + unitMat s j).mulVecLin := by
  classical
  rw [lt_iff_le_and_ne]
  constructor
  · rintro v hv
    rw [LinearMap.mem_range] at hv ⊢
    obtain ⟨w, rfl⟩ := hv
    refine ⟨w - (w j / x j) • x, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_smul, hx, smul_zero, sub_zero, unitMat_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, div_mul_cancel₀ _ hxj, sub_self, zero_smul, add_zero]
  · intro heq
    have hmem : Pi.single s (1 : ℝ) ∈ LinearMap.range (D + unitMat s j).mulVecLin := by
      rw [LinearMap.mem_range]
      refine ⟨(x j)⁻¹ • x, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.mulVec_smul, hx, smul_zero, zero_add,
        unitMat_mulVec, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hxj, one_smul]
    rw [← heq, LinearMap.mem_range] at hmem
    obtain ⟨w, hw⟩ := hmem
    rw [Matrix.mulVecLin_apply] at hw
    have h1 : y ⬝ᵥ (D.mulVec w) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hy, zero_dotProduct]
    rw [hw, dotProduct_single, mul_one] at h1
    exact hys h1

theorem rank_lt {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (D : Matrix I J ℝ) (s : I) (j : J) (x : J → ℝ) (hx : D.mulVec x = 0) (hxj : x j ≠ 0)
    (y : I → ℝ) (hy : D.transpose.mulVec y = 0) (hys : y s ≠ 0) :
    D.rank < (D + unitMat s j).rank := by
  unfold Matrix.rank
  exact Submodule.finrank_lt_finrank_of_lt (range_lt D s j x hx hxj y hy hys)

end OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_2

open OAI.SeymourSecondNeighborhood.Sol_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_2 in
open OAI.SeymourSecondNeighborhood in
theorem solution {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (T : Finset (I × J)) (D : Matrix I J ℝ) (hD : ∀ i j, (i, j) ∉ T → D i j = 0)
    (hmax : ∀ D' : Matrix I J ℝ, (∀ i j, (i, j) ∉ T → D' i j = 0) → D'.rank ≤ D.rank)
    (x : J → ℝ) (hx : D.mulVec x = 0) (y : I → ℝ) (hy : D.transpose.mulVec y = 0)
    (s : I) (j : J) (hsj : (s, j) ∈ T) : x j * y s = 0 := by
  by_contra hne
  have hxj : x j ≠ 0 := left_ne_zero_of_mul hne
  have hys : y s ≠ 0 := right_ne_zero_of_mul hne
  have hsupp : ∀ i j', (i, j') ∉ T → (D + unitMat s j) i j' = 0 := by
    intro i j' h
    rw [Matrix.add_apply, hD i j' h, unitMat_apply_of_not_mem T s j hsj i j' h, add_zero]
  exact absurd (hmax _ hsupp) (not_le.mpr (rank_lt D s j x hx hxj y hy hys))
