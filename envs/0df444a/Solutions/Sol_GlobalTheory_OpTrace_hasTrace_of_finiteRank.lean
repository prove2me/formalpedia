-- Prove2me | solution 1 for GlobalTheory.OpTrace.hasTrace_of_finiteRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:28.393779+00:00
-- url     : https://prove2.me/submissions/a1a8158c-9056-493d-97d3-01f87e612eac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_comp
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_trace_comp_comp

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.OpTrace
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) [FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))] :
    HasTrace T (finRankTrace (T : H →ₗ[ℂ] H)) := by
  let R := LinearMap.range (T : H →ₗ[ℂ] H)
  have : CompleteSpace R := FiniteDimensional.complete ℂ R
  let c : H →L[ℂ] R := T.codRestrict R fun x => ⟨x, rfl⟩
  have h := isTraceClass_of_finiteDimensional (ContinuousLinearMap.id ℂ R)
  refine ⟨h.comp_comp R.subtypeL c, (h.trace_comp_comp R.subtypeL c).trans ?_⟩
  rw [trace_eq_linearMap_trace]
  rfl
end GlobalTheory.OpTrace
