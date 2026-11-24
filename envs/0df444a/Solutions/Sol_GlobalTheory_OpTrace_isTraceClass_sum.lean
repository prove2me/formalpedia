-- Prove2me | solution 1 for GlobalTheory.OpTrace.isTraceClass_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:16:11.398894+00:00
-- url     : https://prove2.me/submissions/51cef610-3416-42cc-8de0-0e216bdd103b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_isTraceClass_zero
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_add

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
    (h : ∀ a ∈ s, IsTraceClass (T a)) : IsTraceClass (∑ a ∈ s, T a) :=
  Finset.sum_induction T IsTraceClass (fun _ _ => IsTraceClass.add) isTraceClass_zero h
end GlobalTheory.OpTrace
