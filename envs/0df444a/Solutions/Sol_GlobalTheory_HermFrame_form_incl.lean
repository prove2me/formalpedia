-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:53.955671+00:00
-- url     : https://prove2.me/submissions/64684a33-a5d2-453c-a470-fe41cf8e1aec

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_form_mulVec
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
theorem _root_.solution (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) (u u' : m → ℂ) :
    form H (incl m l *ᵥ u) (incl m l *ᵥ u') = form (subGram H) u u' := by
  rw [form_mulVec, form]
  congr 2
  conv_lhs => rw [← fromBlocks_toBlocks H]
  simp [incl, subGram, transpose_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    transpose_fromCols, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
end GlobalTheory.HermFrame
