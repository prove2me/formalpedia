-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsTraceClass.summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:23.6648+00:00
-- url     : https://prove2.me/submissions/7e1c2de2-8e46-4e81-b469-4f007644064e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {ι κ : Type*}
namespace GlobalTheory.OpTrace
namespace IsTraceClass
theorem _root_.solution {T : H →L[ℂ] H} (h : IsTraceClass T) (e : HilbertBasis ι ℂ H) :
    Summable fun i => ‖⟪e i, T (e i)⟫_ℂ‖ :=
  (h.hasSum_trace e).summable.norm
end IsTraceClass
end GlobalTheory.OpTrace
