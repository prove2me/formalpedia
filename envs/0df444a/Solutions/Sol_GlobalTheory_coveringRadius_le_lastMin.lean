-- Prove2me | solution 1 for GlobalTheory.coveringRadius_le_lastMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:08:55.752168+00:00
-- url     : https://prove2.me/submissions/5e48dbb3-d9c1-4357-ade3-9b17b570bbef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_lastMin
import Theorems.Thm_GlobalTheory_coveringRadius_le


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
    [DiscreteTopology L] [IsZLattice ℝ L] :
    coveringRadius L ≤ √(finrank ℝ E) / 2 * lastMin L :=
  coveringRadius_le (exists_mem_norm_sub_le_lastMin L)
end GlobalTheory
