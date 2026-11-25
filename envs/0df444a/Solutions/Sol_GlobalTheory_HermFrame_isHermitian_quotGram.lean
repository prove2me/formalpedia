-- Prove2me | solution 1 for GlobalTheory.HermFrame.isHermitian_quotGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:43.406673+00:00
-- url     : https://prove2.me/submissions/0b364a32-f984-4618-844f-4d3d2decea12

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_isHermitian_subGram
import Theorems.Thm_P2M_GlobalTheory_HermFrame_conjTranspose_toBlocks___d5df6ab04568

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}
omit [Fintype l] [DecidableEq l]
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : H.IsHermitian) : (quotGram H).IsHermitian := by
  have h1 : H.toBlocks₁₁.IsHermitian := isHermitian_subGram h
  have h2 : H.toBlocks₂₂.IsHermitian := h.submatrix Sum.inr
  rw [quotGram, ← conjTranspose_toBlocks₁₂ h]
  refine h2.sub ?_
  rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h1.inv.eq,
    Matrix.mul_assoc]
end GlobalTheory.HermFrame
