-- Prove2me | solution 1 for GlobalTheory.CubeFrame.sum_halfPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:50.153668+00:00
-- url     : https://prove2.me/submissions/38fc0e46-bab6-4b19-a2ea-8d89eeb77f81

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
theorem _root_.solution (w : E) : ∑ a ∈ ({0, 1} : Finset (Fin 3)), halfPoint w a = w := by
  simp [halfPoint, ← add_smul]
  norm_num
end GlobalTheory.CubeFrame
