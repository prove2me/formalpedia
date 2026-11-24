-- Prove2me | solution 1 for GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:27.23955+00:00
-- url     : https://prove2.me/submissions/d08a113e-12c2-41c6-9ffc-ed47faf352c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeProdNormSqEqAbsNormSpan
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeProdNormSqEqAbsNormSpanStatement
import Theorems.Thm_GlobalTheory_CMTypeNorm_prod_norm_sq_eq_absNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ α : 𝓞 K, ∏ i, ‖φ i (α : K)‖ ^ 2 = ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm | exact GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm | (intros; apply GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm <;> assumption)
end _root_.GlobalTheory.T
