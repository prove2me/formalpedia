-- Prove2me | solution 1 for GlobalTheory.HermFrame.norm_form_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:53.764848+00:00
-- url     : https://prove2.me/submissions/a545d1a8-0270-4a64-b0d6-b9921bf43d8a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_norm_form_le

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
variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}
namespace GlobalTheory.HermFrame
theorem _root_.solution (hH : H.PosDef) (T : Matrix m m ℂ) (v : m → ℂ) :
    ‖form H (T *ᵥ v) v‖ ≤ opNorm H H T * gnorm H v ^ 2 := by
  refine (norm_form_le hH.posSemidef _ _).trans ?_
  rw [sq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (gnorm_mulVec_le hH hH.posSemidef T v) (gnorm_nonneg _ _)
end GlobalTheory.HermFrame
