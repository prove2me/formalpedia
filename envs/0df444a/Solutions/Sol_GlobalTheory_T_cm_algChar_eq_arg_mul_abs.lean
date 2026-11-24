-- Prove2me | solution 1 for GlobalTheory.T.cm_algChar_eq_arg_mul_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:28.375116+00:00
-- url     : https://prove2.me/submissions/e6d7a273-b276-4d7d-9f5c-34fd9bd1d355

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbs
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbsStatement
import Theorems.Thm_GlobalTheory_Div_CMAlgChar_algChar_eq_arg_mul_abs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by
  first | exact @GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs | exact GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs | (intros; apply GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs <;> assumption)
end _root_.GlobalTheory.T
