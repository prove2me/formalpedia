-- Prove2me | solution 1 for GlobalTheory.HaarAlg.avg_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:28.040832+00:00
-- url     : https://prove2.me/submissions/016c710c-b052-47a6-a239-b0ac133384c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsAlgebraicIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.HaarAlg
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Group K] [IsTopologicalGroup K] [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.HaarAlg
theorem _root_.solution (M : Matrix ι ι ℂ) : avg κ (fun _ => M) = M := by
  ext a b
  simp [avg]
end GlobalTheory.HaarAlg
