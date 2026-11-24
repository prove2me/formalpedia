-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsTraceClass.trace_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:27:21.119304+00:00
-- url     : https://prove2.me/submissions/a0768347-eb6e-4348-be68-267e5a08642d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_trace_comp_comp

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
theorem _root_.solution {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H ≃L[ℂ] K) :
    trace ((A : H →L[ℂ] K) ∘L T ∘L (A.symm : K →L[ℂ] H)) = trace T := by
  rw [h.trace_comp_comp]
  congr 1
  ext x; simp
end IsTraceClass
end GlobalTheory.OpTrace
