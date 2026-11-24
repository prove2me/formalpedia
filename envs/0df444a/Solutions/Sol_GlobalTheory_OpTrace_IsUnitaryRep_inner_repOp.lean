-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.inner_repOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:54:54.771219+00:00
-- url     : https://prove2.me/submissions/4315d350-5c15-4f56-b176-9fa2d5681db2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_isRepOp
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
namespace IsUnitaryRep
theorem _root_.solution (hπ : IsUnitaryRep π) (hf : Continuous f)
    (hc : HasCompactSupport f) (w v : H) :
    ⟪w, repOp π μ f v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ := by
  rw [hπ.repOp_apply hf hc, ← integral_inner (hπ.isRepOp hf hc v).1]
  simp only [inner_smul_right]
end IsUnitaryRep
end GlobalTheory.OpTrace
