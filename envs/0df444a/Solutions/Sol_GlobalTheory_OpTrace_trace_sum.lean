-- Prove2me | solution 1 for GlobalTheory.OpTrace.trace_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:33.053869+00:00
-- url     : https://prove2.me/submissions/7ace43aa-36c3-48b3-838a-f130bd72d41b

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
theorem _root_.solution {α : Type*} (s : Finset α) {T : α → (H →L[ℂ] H)}
    (h : ∀ a ∈ s, IsTraceClass (T a)) : trace (∑ a ∈ s, T a) = ∑ a ∈ s, trace (T a) := by
  have := hasSum_sum fun a (ha : a ∈ s) => (h a ha).hasSum_trace (stdBasis H)
  simpa only [trace, ContinuousLinearMap.sum_apply, inner_sum] using this.tsum_eq
end GlobalTheory.OpTrace
