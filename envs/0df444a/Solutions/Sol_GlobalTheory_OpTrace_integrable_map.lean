-- Prove2me | solution 1 for GlobalTheory.OpTrace.integrable_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:06:01.066592+00:00
-- url     : https://prove2.me/submissions/dc8fa000-af8a-4ab1-80cf-15d8b72dfbdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_left

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
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace G]
variable [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  {ρ : Representation ℂ G V} {f f' : G → ℂ}
omit [Module ℂ V]
namespace GlobalTheory.OpTrace
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] {F : G → V} (hF : IsLocallyConstant F)
    (hc : HasCompactSupport F) (l : V → E) (hl : l 0 = 0) : Integrable (fun g => l (F g)) μ :=
  (hF.comp l).continuous.integrable_of_hasCompactSupport (hc.comp_left hl)
end GlobalTheory.OpTrace
