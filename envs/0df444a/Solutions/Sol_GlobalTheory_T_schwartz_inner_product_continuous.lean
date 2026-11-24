-- Prove2me | solution 1 for GlobalTheory.T.schwartz_inner_product_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:47.146492+00:00
-- url     : https://prove2.me/submissions/ea9ec30a-dd58-4d09-a326-c1c79729cfe7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzInnerProductContinuous
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzInnerProductContinuousStatement
import Theorems.Thm_GlobalTheory_schwartz_pairing_conj_clm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by
  first | exact @GlobalTheory.schwartz_pairing_conj_clm | exact GlobalTheory.schwartz_pairing_conj_clm | (intros; apply GlobalTheory.schwartz_pairing_conj_clm <;> assumption)
end _root_.GlobalTheory.T
