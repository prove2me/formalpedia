-- Prove2me | solution 1 for GlobalTheory.eq_cols_mul_inv_minor_mul_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:50.612797+00:00
-- url     : https://prove2.me/submissions/1f3fa334-39d8-476d-ba6f-eee0d9b0c149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsColsDetNeZeroOfMul

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
theorem _root_.solution {Ω : Type} [Field Ω] {n r : ℕ}
    (π : Matrix (Fin n) (Fin n) Ω) (hπ : π.rank = r) (ι κ : Fin r → Fin n)
    (hd : (π.submatrix ι κ).det ≠ 0) :
    π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id := by
  have hu : IsUnit (π.submatrix ι κ).det := isUnit_iff_ne_zero.mpr hd
  have hC : π.submatrix id κ = π * (1 : Matrix (Fin n) (Fin n) Ω).submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hA : π.submatrix ι κ
      = (1 : Matrix (Fin n) (Fin n) Ω).submatrix ι id * π.submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hrA : (π.submatrix ι κ).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hle : LinearMap.range (π.submatrix id κ).mulVecLin ≤ LinearMap.range π.mulVecLin := by
    rw [hC, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hr : π.rank ≤ (π.submatrix id κ).rank := by
    rw [hπ]
    calc r = (π.submatrix ι κ).rank := hrA.symm
      _ ≤ (π.submatrix id κ).rank := by
        conv_lhs => rw [hA]
        exact Matrix.rank_mul_le_right _ _
  have heq := Submodule.eq_of_le_of_finrank_le hle hr
  have hcol : ∀ j : Fin n, ∃ c : Fin r → Ω, (π.submatrix id κ) *ᵥ c = fun i => π i j := by
    intro j
    have : (fun i => π i j) ∈ LinearMap.range π.mulVecLin :=
      ⟨Pi.single j 1, by ext i; simp⟩
    rw [← heq] at this
    exact this
  choose c hc using hcol
  set X : Matrix (Fin r) (Fin n) Ω := Matrix.of fun a j => c j a with hX
  have h1 : π = π.submatrix id κ * X := by
    ext i j
    have := congrFun (hc j) i
    rw [← this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]
  have h2 : π.submatrix ι id = π.submatrix ι κ * X := by
    ext i j
    have := congrFun (congrFun h1 (ι i)) j
    simpa [Matrix.mul_apply] using this
  rw [h2, Matrix.mul_assoc, ← Matrix.mul_assoc (π.submatrix ι κ)⁻¹, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]
  exact h1
end GlobalTheory
