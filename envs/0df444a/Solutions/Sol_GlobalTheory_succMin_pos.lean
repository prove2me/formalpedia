-- Prove2me | solution 1 for GlobalTheory.succMin_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:20.159801+00:00
-- url     : https://prove2.me/submissions/c0089f84-0a22-46d4-8748-3f44e9f96d44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_succMinOf_pos
import Theorems.Thm_GlobalTheory_natCast_le_rank_of_le_finrank
import Theorems.Thm_GlobalTheory_finite_mem_and_norm_le

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
theorem _root_.solution [FiniteDimensional ℝ E] [DiscreteTopology L] (h1 : 1 ≤ i)
    (hi : i ≤ finrank ℝ (span ℝ (L : Set E))) : 0 < succMin L i :=
  succMinOf_pos (finite_mem_and_norm_le L) (fun _ _ h => norm_pos_iff.2 h) h1
    (natCast_le_rank_of_le_finrank hi)
end GlobalTheory
