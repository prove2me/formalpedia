-- Prove2me | solution 1 for GlobalTheory.T.cm_type_trace_imaginary_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:14:03.022863+00:00
-- url     : https://prove2.me/submissions/f127ebdc-100a-4c79-bcdd-66629f2cc665

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeTraceImaginaryPart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeTraceImaginaryPartStatement
import Theorems.Thm_GlobalTheory_cmType_trace_im_coeff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (h : I → ℝ) (mu : E), (∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, h i * (φ i z).im) →
    ∀ i, 2 * Complex.I * φ i mu = (h i : ℂ) := by
  first | exact @GlobalTheory.cmType_trace_im_coeff | exact GlobalTheory.cmType_trace_im_coeff | (intros; apply GlobalTheory.cmType_trace_im_coeff <;> assumption)
end _root_.GlobalTheory.T
