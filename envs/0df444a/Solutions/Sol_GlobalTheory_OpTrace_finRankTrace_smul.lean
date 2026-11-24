-- Prove2me | solution 1 for GlobalTheory.OpTrace.finRankTrace_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:16:09.38904+00:00
-- url     : https://prove2.me/submissions/4390088e-9467-4dfb-8a84-a0c6819e9c93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_eq

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
theorem _root_.solution (c : ℂ) (T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range T)] :
    finRankTrace (c • T) = c * finRankTrace T := by
  rw [finRankTrace_eq (c • T) (LinearMap.range T)
    fun x => Submodule.smul_mem _ c (LinearMap.mem_range_self T x), finRankTrace, ← smul_eq_mul,
    ← map_smul]
  rfl
end GlobalTheory.OpTrace
