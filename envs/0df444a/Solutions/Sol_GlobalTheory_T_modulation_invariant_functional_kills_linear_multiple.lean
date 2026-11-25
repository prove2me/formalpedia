-- Prove2me | solution 1 for GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:26:52.764413+00:00
-- url     : https://prove2.me/submissions/97c0ac91-26eb-44cc-8a85-ba1f35b6b390

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationInvariantFunctionalLinearZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationInvariantFunctionalLinearZeroStatement
import Theorems.Thm_GlobalTheory_CharInvForm_kills_linear_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by
  first | exact @GlobalTheory.CharInvForm.kills_linear_mul | exact GlobalTheory.CharInvForm.kills_linear_mul | (intros; apply GlobalTheory.CharInvForm.kills_linear_mul <;> assumption)
end _root_.GlobalTheory.T
