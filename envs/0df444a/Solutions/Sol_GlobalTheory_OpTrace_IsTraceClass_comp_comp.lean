-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsTraceClass.comp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:32:48.665004+00:00
-- url     : https://prove2.me/submissions/5302c048-96ef-42a7-acb1-6a4f044a4be9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_isTraceClass_sum

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
    (A' : K →L[ℂ] H) : IsTraceClass (A ∘L T ∘L A') := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  have : A ∘L (∑ i, B i ∘L C i) ∘L A' = ∑ i, (A ∘L B i) ∘L (C i ∘L A') := by
    ext x; simp
  rw [this]
  exact isTraceClass_sum _ fun i _ => ((hB i).comp_left A).isTraceClass_comp ((hC i).comp_right A')
end IsTraceClass
end GlobalTheory.OpTrace
