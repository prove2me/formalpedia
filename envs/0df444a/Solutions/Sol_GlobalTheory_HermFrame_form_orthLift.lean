-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_orthLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:50.559102+00:00
-- url     : https://prove2.me/submissions/3ab06ad8-fea5-48df-b2c3-9e92c5766e77

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
theorem _root_.solution (hu : IsUnit (subGram H).det) (q q' : l → ℂ) :
    form H (orthLift H *ᵥ q) (orthLift H *ᵥ q') = form (quotGram H) q q' := by
  rw [form_mulVec, orthLift_transpose_mul hu, form]
  simp [orthLift, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols,
    fromCols_mul_fromRows]
end GlobalTheory.HermFrame
