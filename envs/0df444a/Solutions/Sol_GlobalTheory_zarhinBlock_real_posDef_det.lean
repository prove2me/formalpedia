-- Prove2me | solution 1 for GlobalTheory.zarhinBlock_real_posDef_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:27.067118+00:00
-- url     : https://prove2.me/submissions/a22d7259-dcb6-4689-9abe-f3be2d1f775b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntMatrixTransposeMulEqSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Kronecker
open GlobalTheory
variable {n q : Type} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q]
namespace GlobalTheory
theorem _root_.solution (B A : Matrix n n ℝ) (x : Matrix q q ℝ) (s : ℝ)
    (hB : B.PosDef) (hA : A = (1 + s) • B⁻¹) (hx : xᵀ * x = s • (1 : Matrix q q ℝ)) :
    (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) ((1 : Matrix n n ℝ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℝ))).PosDef ∧
      (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) ((1 : Matrix n n ℝ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℝ))).det = 1 := by
  have hdet : IsUnit B.det := hB.det_pos.ne'.isUnit
  have hK : (B ⊗ₖ (1 : Matrix q q ℝ)).PosDef := hB.kronecker PosDef.one
  have hKi : (B⁻¹ ⊗ₖ (1 : Matrix q q ℝ)).PosDef := hB.inv.kronecker PosDef.one
  letI := hK.isUnit.invertible
  have hinv : (B ⊗ₖ (1 : Matrix q q ℝ))⁻¹ = B⁻¹ ⊗ₖ (1 : Matrix q q ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [← mul_kronecker_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, one_kronecker_one]
  have hS : A ⊗ₖ (1 : Matrix q q ℝ) - ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) * (B ⊗ₖ (1 : Matrix q q ℝ))⁻¹ *
      ((1 : Matrix n n ℝ) ⊗ₖ x) = B⁻¹ ⊗ₖ (1 : Matrix q q ℝ) := by
    rw [hinv, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_one, hx, hA, kronecker_smul, smul_kronecker, add_smul, one_smul,
      add_sub_cancel_right]
  have hT : ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)ᴴ = (1 : Matrix n n ℝ) ⊗ₖ x := by
    rw [conjTranspose_eq_transpose_of_trivial, ← kroneckerMap_transpose, transpose_one,
      transpose_transpose]
  have hd : (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)
      ((1 : Matrix n n ℝ) ⊗ₖ x) (B ⊗ₖ (1 : Matrix q q ℝ))).det = 1 := by
    rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv, hS, ← det_mul, ← mul_kronecker_mul,
      Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, one_kronecker_one, det_one]
  refine ⟨?_, hd⟩
  have hps : (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)
      ((1 : Matrix n n ℝ) ⊗ₖ x) (B ⊗ₖ (1 : Matrix q q ℝ))).PosSemidef := by
    have := (PosDef.fromBlocks₂₂ (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) hK).mpr
      (by rw [hT, hS]; exact hKi.posSemidef)
    rwa [hT] at this
  exact hps.posDef_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (by rw [hd]; exact isUnit_one))
end GlobalTheory
