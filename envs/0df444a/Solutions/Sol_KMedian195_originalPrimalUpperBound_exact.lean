-- Prove2me | solution 1 for KMedian195.originalPrimalUpperBound_exact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:03:06.451735+00:00
-- url     : https://prove2.me/submissions/4ff56262-78a9-4ca6-a40e-8afa758bd356

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3



@[expose] public section

namespace KMedian195

noncomputable section

/-- The exact factor-revealing bound throughout the closed parameter interval `[1, 1.224]`. -/
theorem originalPrimalUpperBound_exact
    (gamma : ℝ) (hγlo : 1 ≤ gamma) (hγhi : gamma ≤ (153 : ℝ) / 125) :
    OriginalPrimalUpperBound gamma (2 - (gamma - 1) ^ 2) := by
  rcases eq_or_lt_of_le hγlo with hγ | hγ
  · subst gamma
    simpa using originalPrimalUpperBound_one
  · exact originalPrimalUpperBound_exact_of_one_lt hγ hγhi

end

end KMedian195

end

public section

theorem solution : type_of% @KMedian195.originalPrimalUpperBound_exact := @KMedian195.originalPrimalUpperBound_exact
