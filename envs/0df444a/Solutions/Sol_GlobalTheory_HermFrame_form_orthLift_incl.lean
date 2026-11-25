-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_orthLift_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:59.697944+00:00
-- url     : https://prove2.me/submissions/41ea4851-9076-472d-a928-d3a80658deae

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_form_mulVec
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_HermFrame_orthLift_transpose_mul
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
theorem _root_.solution (hu : IsUnit (subGram H).det) (q : l → ℂ) (u : m → ℂ) :
    form H (orthLift H *ᵥ q) (incl m l *ᵥ u) = 0 := by
  rw [form_mulVec, orthLift_transpose_mul hu]
  simp [incl, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols,
    fromCols_mul_fromRows]
end GlobalTheory.HermFrame
