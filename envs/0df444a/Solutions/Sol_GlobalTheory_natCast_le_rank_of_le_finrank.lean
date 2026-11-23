-- Prove2me | solution 1 for GlobalTheory.natCast_le_rank_of_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:39.636378+00:00
-- url     : https://prove2.me/submissions/7da80b42-51f8-49be-88fb-1799e719cdf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin

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
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}
namespace GlobalTheory
theorem _root_.solution {K W : Type*} [DivisionRing K] [AddCommGroup W] [Module K W]
    (h : i ≤ finrank K W) : (i : Cardinal) ≤ Module.rank K W :=
  natCast_le_rank_iff.2 (exists_linearIndependent_of_le_finrank h)
end GlobalTheory
