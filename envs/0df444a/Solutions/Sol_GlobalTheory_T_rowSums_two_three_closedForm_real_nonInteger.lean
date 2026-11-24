-- Prove2me | solution 1 for GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:16.59557+00:00
-- url     : https://prove2.me/submissions/8a0a6398-716c-4b89-bcad-83c08c7eddd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonInteger
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonIntegerStatement
import Theorems.Thm_GlobalTheory_WpFam_RowReal_row_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ w : ℂ, w.im = 0 → (∀ n : ℤ, w ≠ n) → (∑' m : ℤ, 1 / (w + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 2)) ∧ ∑' m : ℤ, 1 / (w + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 3) := by
  first | exact @GlobalTheory.WpFam.RowReal.row_real | exact GlobalTheory.WpFam.RowReal.row_real | (intros; apply GlobalTheory.WpFam.RowReal.row_real <;> assumption)
end _root_.GlobalTheory.T
