-- Prove2me | solution 1 for GlobalTheory.hasDerivAt_of_continuous_additive_to_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:16.607376+00:00
-- url     : https://prove2.me/submissions/f842d1b1-e424-400f-ab6d-0a2123f1031b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtOfContinuousOfMapAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtOfContinuousRealToComplexExponential
import Theorems.Thm_GlobalTheory_DerivativeOfAdditiveContinuous_hasDerivAt_of_continuous_of_map_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (χ : ℝ → ℂ) (hc : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) (h0 : χ 0 = 1) :
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first
  | exact @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | (apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add ..)
end GlobalTheory
