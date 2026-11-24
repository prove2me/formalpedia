-- Prove2me | solution 1 for GlobalTheory.IsSiegel.neg_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:27.340856+00:00
-- url     : https://prove2.me/submissions/56cf1d08-8e74-4bae-9f5a-c1c3c7d59168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_IsSiegel_exists_eq_transpose_mul_diagonal_mul
import Theorems.Thm_GlobalTheory_inv_map_ofReal
import Theorems.Thm_GlobalTheory_IsSiegel_transpose_mul_mul
import Theorems.Thm_GlobalTheory_inv_diagonal_of_ne_zero
import Theorems.Thm_GlobalTheory_isSiegel_diagonal_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {σ : Matrix ι ι ℂ} (h : IsSiegel σ) : IsSiegel (-σ⁻¹) := by
  obtain ⟨P, hP, t, ht, rfl⟩ := h.exists_eq_transpose_mul_diagonal_mul
  have ht0 (i : ι) : t i ≠ 0 := fun h0 => by simpa [h0] using ht i
  have h1 : IsSiegel (diagonal fun i => -(t i)⁻¹) := isSiegel_diagonal_iff.2 fun i => by
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos (ht i) (normSq_pos.2 (ht0 i))
  have h2 : (P⁻¹ᵀ).det ≠ 0 := by
    rw [det_transpose]
    exact (isUnit_nonsing_inv_det _ hP.isUnit).ne_zero
  convert h1.transpose_mul_mul h2 using 1
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_diagonal_of_ne_zero ht0,
    ← transpose_nonsing_inv, inv_map_ofReal hP, transpose_map, transpose_transpose,
    ← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
end IsSiegel
end GlobalTheory
