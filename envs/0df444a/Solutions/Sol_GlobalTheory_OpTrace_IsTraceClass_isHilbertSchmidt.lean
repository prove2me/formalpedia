-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsTraceClass.isHilbertSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:16.661593+00:00
-- url     : https://prove2.me/submissions/2e79de3e-cd01-4c83-8329-4311d9e26914

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_isHilbertSchmidt_zero
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_add
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_left

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
theorem _root_.solution {T : H →L[ℂ] H} (h : IsTraceClass T) :
    IsHilbertSchmidt T := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  exact Finset.sum_induction _ IsHilbertSchmidt (fun _ _ => IsHilbertSchmidt.add)
    isHilbertSchmidt_zero fun i _ => (hC i).comp_left _
end IsTraceClass
end GlobalTheory.OpTrace
