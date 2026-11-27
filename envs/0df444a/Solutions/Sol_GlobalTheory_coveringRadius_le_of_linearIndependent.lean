-- Prove2me | solution 1 for GlobalTheory.coveringRadius_le_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:18.640031+00:00
-- url     : https://prove2.me/submissions/050a0374-b1d1-4dfb-8b88-380726a4ba58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_norm_sub_le_of_linearIndependent
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
theorem _root_.solution [FiniteDimensional ℝ E] {ι : Type*}
    [Fintype ι] {v : ι → E} {r : ℝ} (hv : LinearIndependent ℝ v)
    (hn : Fintype.card ι = finrank ℝ E) (hL : ∀ i, v i ∈ L) (hr : ∀ i, ‖v i‖ ≤ r) :
    coveringRadius L ≤ √(finrank ℝ E) / 2 * r :=
  coveringRadius_le (exists_mem_norm_sub_le_of_linearIndependent hv hn hL hr)
end GlobalTheory
