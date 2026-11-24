-- Prove2me | solution 1 for GlobalTheory.CubeFrame.norm_sum_halfPoint_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:49.491313+00:00
-- url     : https://prove2.me/submissions/78d6e86b-7098-4248-8888-b79e43f36b79

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
theorem _root_.solution (w : E) {I : Finset (Fin 3)} (hI : I ≠ {0, 1}) :
    ‖∑ a ∈ I, halfPoint w a‖ ≤ ‖w‖ / 2 := by
  have h : ‖(2⁻¹ : ℂ) • w‖ = ‖w‖ / 2 := by
    rw [norm_smul]; simp; ring
  have h0 : (0 : ℝ) ≤ ‖w‖ / 2 := by positivity
  have hI' : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {2} ∨ I = {0, 2} ∨ I = {1, 2} ∨ I = {0, 1, 2} := by
    revert I
    decide
  rcases hI' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [halfPoint, h, h0]
end GlobalTheory.CubeFrame
