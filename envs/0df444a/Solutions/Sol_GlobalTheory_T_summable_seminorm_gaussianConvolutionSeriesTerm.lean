-- Prove2me | solution 1 for GlobalTheory.T.summable_seminorm_gaussianConvolutionSeriesTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:59.199368+00:00
-- url     : https://prove2.me/submissions/917e2d58-a733-4c22-a4c8-21b1f71b1361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableSeminormGaussianConvolutionSeriesTerm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableSeminormGaussianConvolutionSeriesTermStatement
import Theorems.Thm_GlobalTheory_ConvSeries_summable_seminorm_term


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ)
    (t : ℕ → SchwartzMap E ℂ), (∀ j y, t j y = GlobalTheory.ConvSeries.term b c h j y) →
    ∀ (k n : ℕ), Summable (fun j => SchwartzMap.seminorm ℂ k n (t j)) := by
  first | exact @GlobalTheory.ConvSeries.summable_seminorm_term | exact GlobalTheory.ConvSeries.summable_seminorm_term | (intros; apply GlobalTheory.ConvSeries.summable_seminorm_term <;> assumption)
end _root_.GlobalTheory.T
