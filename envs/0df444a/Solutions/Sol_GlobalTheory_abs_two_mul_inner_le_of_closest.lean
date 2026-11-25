-- Prove2me | solution 1 for GlobalTheory.abs_two_mul_inner_le_of_closest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:10:02.785675+00:00
-- url     : https://prove2.me/submissions/9a48b6d7-b8fe-4afc-b15b-e7967de45050

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_abs_two_mul_inner_le_of_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}
namespace GlobalTheory
theorem _root_.solution {p w : E} (hw : w ∈ L)
    (h : ∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) {y : E} (hy : y ∈ L) : |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2 :=
  abs_two_mul_inner_le_of_norm_le
    ((h _ (sub_mem hw hy)).trans_eq (by congr 1; abel))
    ((h _ (add_mem hw hy)).trans_eq (by congr 1; abel))
end GlobalTheory
