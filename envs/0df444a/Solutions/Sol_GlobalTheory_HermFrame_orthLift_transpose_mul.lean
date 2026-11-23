-- Prove2me | solution 1 for GlobalTheory.HermFrame.orthLift_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:21.957+00:00
-- url     : https://prove2.me/submissions/f1572cbf-559b-44a9-84a2-224d612efa8f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}
namespace GlobalTheory.HermFrame
theorem _root_.solution (hu : IsUnit (subGram H).det) :
    (orthLift H)ᵀ * H = fromCols 0 (quotGram H) := by
  have h : (orthLift H)ᵀ = fromCols (-(H.toBlocks₂₁ * H.toBlocks₁₁⁻¹)) 1 := by
    simp [orthLift, orthCoeff, transpose_fromRows, transpose_nonsing_inv]
  rw [h]
  conv_lhs => rhs; rw [← fromBlocks_toBlocks H]
  rw [fromCols_mul_fromBlocks]
  congr 1
  · rw [Matrix.neg_mul, nonsing_inv_mul_cancel_right H.toBlocks₁₁ _ hu]; simp
  · rw [quotGram]; simp [sub_eq_neg_add]
end GlobalTheory.HermFrame
