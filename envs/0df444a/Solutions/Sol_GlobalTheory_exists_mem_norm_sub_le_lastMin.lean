-- Prove2me | solution 1 for GlobalTheory.exists_mem_norm_sub_le_lastMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:15.449641+00:00
-- url     : https://prove2.me/submissions/8c3114f7-05a5-4336-bb73-c389dc9d6fd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_lastMin_of_mem_span
import Theorems.Thm_GlobalTheory_finrank_span_eq_finrank_int
import Theorems.Thm_GlobalTheory_finrank_span_of_isZLattice


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
theorem _root_.solution [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (x : E) :
    ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℝ E) / 2 * lastMin L := by
  have := exists_mem_norm_sub_le_lastMin_of_mem_span L (x := x)
    (by rw [IsZLattice.span_top]; exact mem_top)
  rwa [← finrank_span_eq_finrank_int, finrank_span_of_isZLattice] at this
end GlobalTheory
