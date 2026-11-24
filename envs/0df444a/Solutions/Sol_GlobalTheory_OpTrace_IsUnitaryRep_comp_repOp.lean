-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.comp_repOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:54:56.583528+00:00
-- url     : https://prove2.me/submissions/f3df92eb-06e4-4b68-bda6-d04cef9b8dba

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
theorem _root_.solution {π' : G →* (K →L[ℂ] K)} (hπ : IsUnitaryRep π)
    (hπ' : IsUnitaryRep π') (hf : Continuous f) (hc : HasCompactSupport f) (A : H →L[ℂ] K)
    (hA : ∀ g v, A (π g v) = π' g (A v)) : A ∘L repOp π μ f = repOp π' μ f ∘L A := by
  ext v
  rw [comp_apply, comp_apply, hπ.repOp_apply hf hc, hπ'.repOp_apply hf hc,
    ← A.integral_comp_comm (hπ.isRepOp hf hc v).1]
  simp only [map_smul, hA]
end IsUnitaryRep
end GlobalTheory.OpTrace
