-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.repOp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:20.267643+00:00
-- url     : https://prove2.me/submissions/309ba772-2140-49d7-87de-603ff8366537

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsHilbertSchmidt_smul
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_smul
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
theorem _root_.solution (hπ : IsUnitaryRep π) (hf : Continuous f)
    (hc : HasCompactSupport f) (c : ℂ) : repOp π μ (c • f) = c • repOp π μ f := by
  refine IsRepOp.repOp_eq fun v => ?_
  obtain ⟨h1, h2⟩ := hπ.isRepOp (μ := μ) hf hc v
  simp only [Pi.smul_apply, smul_assoc, smul_apply]
  exact ⟨h1.smul c, by rw [integral_smul, h2]⟩
end IsUnitaryRep
end GlobalTheory.OpTrace
