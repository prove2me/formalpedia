-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Assignment.read_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:52.576022+00:00
-- url     : https://prove2.me/submissions/55c26598-2da4-4715-addb-c2a3e9726adc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_invT_mem_KO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip
namespace Assignment
theorem _root_.solution (s : Assignment) {n : Type*} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ KO k n) : s.read g ∈ KO k n := by
  cases s
  · exact invT_mem_KO hg
  · exact hg
end Assignment
end GlobalTheory.SplitFlip
