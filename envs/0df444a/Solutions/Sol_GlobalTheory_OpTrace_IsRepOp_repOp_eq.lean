-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsRepOp.repOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:40.549288+00:00
-- url     : https://prove2.me/submissions/72a29a9d-d1cb-4099-8f6c-33b3f7299332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional

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
omit [TopologicalSpace G] [CompleteSpace H]
namespace GlobalTheory.OpTrace
namespace IsRepOp
theorem _root_.solution {T : H →L[ℂ] H} (h : IsRepOp π μ f T) : repOp π μ f = T := by
  have h' : ∃ T, IsRepOp π μ f T := ⟨T, h⟩
  ext v
  rw [repOp, dif_pos h', (h'.choose_spec v).2, (h v).2]
end IsRepOp
end GlobalTheory.OpTrace
