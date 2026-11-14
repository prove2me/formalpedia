-- Prove2me | solution 1 for KMedian195.originalPrimalUpperBound_195
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:03:55.415822+00:00
-- url     : https://prove2.me/submissions/8d018e4c-c376-4621-8614-7049a104b76a

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`, the last three theorems of
`bound-195/KMedian195/FactorRevealingPrimal.lean`. The first and last are the two theorems of
`bound-195/Challenge.lean`, which the source checks with the comparator.
Changes: module header (`module`, `public import`, `@[expose] public section`) and a module
docstring; the theorems are moved here from `Imported/KMedian195/FactorRevealingPrimal.lean`.
-/
module

public import Definitions.Def_KMedian195_FactorRevealingPrimal
public import Theorems.Thm_KMedian195_originalPrimalUpperBound_exact

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3



@[expose] public section

namespace KMedian195

noncomputable section

theorem originalPrimalUpperBound_153_div_125_exact :
    OriginalPrimalUpperBound ((153 : ℝ) / 125)
      (2 - (((153 : ℝ) / 125) - 1) ^ 2) := by
  exact originalPrimalUpperBound_exact _ (by norm_num) le_rfl

theorem originalPrimalUpperBound_195 :
    OriginalPrimalUpperBound ((153 : ℝ) / 125) ((39 : ℝ) / 20) := by
  intro n hn x hx
  have hExact := originalPrimalUpperBound_153_div_125_exact n hn x hx
  have hbound : 2 - (((153 : ℝ) / 125) - 1) ^ 2 ≤ (39 : ℝ) / 20 := by
    norm_num
  exact le_trans hExact hbound

end

end KMedian195

end

public section

theorem solution : type_of% @KMedian195.originalPrimalUpperBound_195 := @KMedian195.originalPrimalUpperBound_195
