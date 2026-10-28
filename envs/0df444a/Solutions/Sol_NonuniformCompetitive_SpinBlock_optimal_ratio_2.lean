-- Prove2me | solution 2 for NonuniformCompetitive.SpinBlock.optimal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:43.496919+00:00
-- url     : https://prove2.me/submissions/81b737ab-2dfd-4221-9297-3e5adb840515

import Mathlib
import Definitions.Def_NonuniformCompetitive_SpinBlock_Randomized
import Definitions.Def_NonuniformCompetitive_SpinBlock_blockCDF
import Theorems.Thm_NonuniformCompetitive_SpinBlock_ratio_attained
import Theorems.Thm_NonuniformCompetitive_SpinBlock_no_better_ratio

-- carved verbatim out of submission 71db7125-46b2-4d78-b1df-c98ac1bca1bb, lines 606-612

section
open NonuniformCompetitive.SpinBlock MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open NonuniformCompetitive.SpinBlock MeasureTheory Set
open scoped Interval
open scoped NNReal ENNReal

theorem solution (C : ℝ) (hC : 0 < C) :
    (∀ (A : NonuniformCompetitive.SpinBlock.RandomizedAlg C) (c : ℝ),
      A.IsCompetitive c → Real.exp 1/(Real.exp 1-1) ≤ c) ∧
    ∃ A : NonuniformCompetitive.SpinBlock.RandomizedAlg C,
      A.IsCompetitive (Real.exp 1/(Real.exp 1-1)) :=
  ⟨fun A c hc => NonuniformCompetitive.SpinBlock.no_better_ratio C hC A c hc,NonuniformCompetitive.SpinBlock.ratio_attained C hC⟩

end
