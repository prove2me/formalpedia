-- Prove2me | solution 1 for GlobalTheory.HaarAlg.avg_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:30.336093+00:00
-- url     : https://prove2.me/submissions/b7839981-38c0-45df-8fa6-39614b8f4502

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
variable [κ.IsMulLeftInvariant]
omit [CompactSpace K] [IsProbabilityMeasure κ] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.HaarAlg
theorem _root_.solution (F : K → Matrix ι ι ℂ) (h : K) : (avg κ fun g => F (h * g)) = avg κ F := by
  ext a b
  exact integral_mul_left_eq_self (fun g => F g a b) h
end GlobalTheory.HaarAlg
