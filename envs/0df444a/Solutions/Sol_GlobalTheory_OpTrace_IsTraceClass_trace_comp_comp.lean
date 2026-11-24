-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsTraceClass.trace_comp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:08:34.480752+00:00
-- url     : https://prove2.me/submissions/88cf958e-2605-45e9-8be7-da86d685efff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_trace_comp_comm
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_left
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_right
import Theorems.Thm_GlobalTheory_OpTrace_trace_sum

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
theorem _root_.solution {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] K)
    (A' : K →L[ℂ] H) : trace (A ∘L T ∘L A') = trace (T ∘L A' ∘L A) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  have h1 : A ∘L (∑ i, B i ∘L C i) ∘L A' = ∑ i, (A ∘L B i) ∘L (C i ∘L A') := by
    ext x; simp
  have h2 : (∑ i, B i ∘L C i) ∘L A' ∘L A = ∑ i, B i ∘L (C i ∘L A' ∘L A) := by
    ext x; simp
  rw [h1, h2, trace_sum _ fun i _ => ((hB i).comp_left A).isTraceClass_comp ((hC i).comp_right A'),
    trace_sum _ fun i _ => (hB i).isTraceClass_comp ((hC i).comp_right _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_comp_comm ((hB i).comp_left A) ((hC i).comp_right A'),
    trace_comp_comm (hB i) ((hC i).comp_right _)]
  rfl
end IsTraceClass
end GlobalTheory.OpTrace
