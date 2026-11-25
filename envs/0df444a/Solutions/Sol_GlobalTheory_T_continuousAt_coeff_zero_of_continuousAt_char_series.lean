-- Prove2me | solution 1 for GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:14:23.816342+00:00
-- url     : https://prove2.me/submissions/895deca4-ee00-4532-a98d-b9856787fec4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZeroStatement
import Theorems.Thm_GlobalTheory_continuousAt_charSeries_coef_zero


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
theorem _root_.solution : ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 := by
  first | exact @GlobalTheory.continuousAt_charSeries_coef_zero | exact GlobalTheory.continuousAt_charSeries_coef_zero | (intros; apply GlobalTheory.continuousAt_charSeries_coef_zero <;> assumption)
end _root_.GlobalTheory.T
