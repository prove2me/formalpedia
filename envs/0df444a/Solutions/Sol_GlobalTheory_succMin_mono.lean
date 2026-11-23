-- Prove2me | solution 1 for GlobalTheory.succMin_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:57.701576+00:00
-- url     : https://prove2.me/submissions/232e48a8-5cc3-4711-a36a-f5dc7f0d2860

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_succMinOf_mono
import Theorems.Thm_GlobalTheory_natCast_le_rank_of_le_finrank

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
theorem _root_.solution (hij : i ≤ j) (hj : j ≤ finrank ℝ (span ℝ (L : Set E))) :
    succMin L i ≤ succMin L j :=
  succMinOf_mono hij (natCast_le_rank_of_le_finrank hj)
end GlobalTheory
