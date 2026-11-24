-- Prove2me | solution 1 for GlobalTheory.CubeFrame.differentiable_halfPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:48.407955+00:00
-- url     : https://prove2.me/submissions/ba71ba4e-c980-4643-931f-0c24821a898d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type} {W : ι → Set E} {c : ι → ι → E → ℂ}
  {T : (Finset (Fin 3) → ι) → (Fin 3 → E) → ℂ}
omit [FiniteDimensional ℂ E]
namespace GlobalTheory.CubeFrame
theorem _root_.solution : Differentiable ℂ (halfPoint : E → Fin 3 → E) := by
  refine differentiable_pi.mpr fun a => ?_
  fin_cases a <;> simp [halfPoint] <;> fun_prop
end GlobalTheory.CubeFrame
