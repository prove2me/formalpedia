-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.repOp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:19.053047+00:00
-- url     : https://prove2.me/submissions/c7a0c042-5c0a-410f-89c7-305657c1a255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_add
import Theorems.Thm_GlobalTheory_OpTrace_IsRepOp_repOp_eq
import Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_isRepOp

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
omit [CompleteSpace H]
namespace GlobalTheory.OpTrace
namespace IsUnitaryRep
theorem _root_.solution (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f)
    (hf' : Continuous f') (hc' : HasCompactSupport f') :
    repOp π μ (f + f') = repOp π μ f + repOp π μ f' := by
  refine IsRepOp.repOp_eq fun v => ?_
  obtain ⟨h1, h2⟩ := hπ.isRepOp (μ := μ) hf hc v
  obtain ⟨h3, h4⟩ := hπ.isRepOp (μ := μ) hf' hc' v
  simp only [Pi.add_apply, add_smul, add_apply]
  exact ⟨h1.add h3, by rw [integral_add h1 h3, h2, h4]⟩
end IsUnitaryRep
end GlobalTheory.OpTrace
