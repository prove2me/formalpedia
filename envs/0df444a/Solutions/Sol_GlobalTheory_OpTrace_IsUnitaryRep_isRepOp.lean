-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.isRepOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:23:20.068843+00:00
-- url     : https://prove2.me/submissions/be095532-20b1-4b72-92bb-3090fb77fc9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsHilbertSchmidt_smul
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_smul
import Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_isRepOp_of_integrable

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
theorem _root_.solution (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f) :
    IsRepOp π μ f (repOp π μ f) :=
  hπ.isRepOp_of_integrable (hf.integrable_of_hasCompactSupport hc) fun v =>
    ((hf.smul (hπ.continuous_apply v)).integrable_of_hasCompactSupport
      hc.smul_right).aestronglyMeasurable
end IsUnitaryRep
end GlobalTheory.OpTrace
