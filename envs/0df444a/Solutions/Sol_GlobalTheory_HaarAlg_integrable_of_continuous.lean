-- Prove2me | solution 1 for GlobalTheory.HaarAlg.integrable_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:31.059008+00:00
-- url     : https://prove2.me/submissions/e985151b-8e7c-433d-8c1f-405f9782a75c

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
omit [Group K] [IsTopologicalGroup K]
namespace GlobalTheory.HaarAlg
theorem _root_.solution {f : K → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
end GlobalTheory.HaarAlg
