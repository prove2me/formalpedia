-- Prove2me | solution 1 for GlobalTheory.WeightedInverseBound.wls_fintype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:36.103823+00:00
-- url     : https://prove2.me/submissions/67736a0a-c3e6-4221-97e7-ee304c18e07e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
import Theorems.Thm_GlobalTheory_T_exists_norm_weighted_least_squares_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open GlobalTheory.WeightedInverseBound
namespace GlobalTheory.WeightedInverseBound
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {g : ℕ} (L : Matrix ι (Fin g) ℝ)
    (hL : L.rank = g) : ∃ K : ℝ, ∀ (D : ι → ℝ) (b : ι → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖
        ≤ K * ‖b‖ := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hr : (L.submatrix e (Equiv.refl (Fin g))).rank = g := by
    rw [Matrix.rank_submatrix]; exact hL
  obtain ⟨K, hK⟩ := GlobalTheory.T.exists_norm_weighted_least_squares_le _ g _ hr
  refine ⟨K, fun D b hD => ?_⟩
  have h := hK (D ∘ e) (b ∘ e) (fun k => hD _)
  have h1 : (L.submatrix e (Equiv.refl (Fin g))).transpose * Matrix.diagonal (D ∘ e) *
      (L.submatrix e (Equiv.refl (Fin g))) = L.transpose * Matrix.diagonal D * L := by
    ext i j
    simp only [Matrix.mul_apply (M := _ * Matrix.diagonal _), Matrix.mul_diagonal,
      Matrix.transpose_apply, Matrix.submatrix_apply, Equiv.refl_apply, Function.comp]
    exact e.sum_comp (fun k => L k i * D k * L k j)
  have h2 : ((L.submatrix e (Equiv.refl (Fin g))).transpose * Matrix.diagonal (D ∘ e)).mulVec
      (b ∘ e) = (L.transpose * Matrix.diagonal D).mulVec b := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal,
      Matrix.transpose_apply, Matrix.submatrix_apply, Equiv.refl_apply, Function.comp]
    exact e.sum_comp (fun k => L k i * D k * b k)
  have h3 : ‖b ∘ e‖ = ‖b‖ := e.surjective.pi_norm_comp b
  rw [h1, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h2, h3] at h
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  exact h
end GlobalTheory.WeightedInverseBound
