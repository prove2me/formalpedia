-- Prove2me | solution 1 for GlobalTheory.OpTrace.repTrace_charRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:54:55.514787+00:00
-- url     : https://prove2.me/submissions/9b94a74e-0f2b-4a4a-8fcb-c96bd6a5d0f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_isUnitaryRep_charRep
import Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_repOp_apply

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
variable {G : Type*} [Group G] [TopologicalSpace G]
  {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [MeasurableSpace G]
variable {π : G →* (H →L[ℂ] H)} {μ : Measure G} {f f' : G → ℂ}
variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
namespace GlobalTheory.OpTrace
theorem _root_.solution {χ : G →* Circle} (hχ : Continuous χ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    HasTrace (repOp (charRep χ) μ f) (∫ g, f g * (χ g : ℂ) ∂μ) := by
  have h : repOp (charRep χ) μ f = (∫ g, f g * (χ g : ℂ) ∂μ) • ContinuousLinearMap.id ℂ ℂ := by
    ext
    rw [(isUnitaryRep_charRep hχ).repOp_apply hf hc]
    simp [charRep]
  refine ⟨isTraceClass_of_finiteDimensional _, ?_⟩
  rw [h]
  simp [trace_smul, trace_eq_linearMap_trace]
end GlobalTheory.OpTrace
