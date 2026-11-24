-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.repOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:38:56.036827+00:00
-- url     : https://prove2.me/submissions/08737c55-2bad-451e-8324-38f1eb1056dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
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
theorem _root_.solution (hπ : IsUnitaryRep π) (hf : Continuous f)
    (hc : HasCompactSupport f) (v : H) : repOp π μ f v = ∫ g, f g • π g v ∂μ :=
  (hπ.isRepOp hf hc v).2
end IsUnitaryRep
end GlobalTheory.OpTrace
