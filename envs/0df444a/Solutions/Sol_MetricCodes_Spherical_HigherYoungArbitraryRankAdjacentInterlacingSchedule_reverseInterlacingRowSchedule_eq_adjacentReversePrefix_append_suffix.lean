-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule.reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/3e96d66f-09a2-4673-a15a-7882c921776a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_le_of_mem_adjacentReversePrefix
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_lt_of_mem_adjacentReverseSuffix

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingTriangularCoefficient
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
theorem _root_.solution
    {r : ℕ} (low : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2)) :
    reverseInterlacingRowSchedule low mu =
      adjacentReversePrefix low mu row ++
        adjacentReverseSuffix low mu row := by
  classical
  let pref := adjacentReversePrefix low mu row
  let suff := adjacentReverseSuffix low mu row
  have hperm : (pref ++ suff).Perm
      (reverseInterlacingRowSchedule low mu) := by
    apply List.perm_iff_count.mpr
    intro i
    rw [List.count_append]
    by_cases hi : row ≤ i
    · have hprefix : pref.count i =
          (reverseInterlacingRowSchedule low mu).count i := by
        exact List.count_filter (by simpa using hi)
      have hsuffix : suff.count i = 0 := by
        apply List.count_eq_zero.mpr
        intro hmem
        have hlt := lt_of_mem_adjacentReverseSuffix
          low mu row i hmem
        exact (not_lt_of_ge hi) hlt
      rw [hprefix, hsuffix, Nat.add_zero]
    · have hlt : i < row := lt_of_not_ge hi
      have hprefix : pref.count i = 0 := by
        apply List.count_eq_zero.mpr
        intro hmem
        exact hi (le_of_mem_adjacentReversePrefix
          low mu row i hmem)
      have hsuffix : suff.count i =
          (reverseInterlacingRowSchedule low mu).count i := by
        exact List.count_filter (by simpa using hlt)
      rw [hprefix, hsuffix, Nat.zero_add]
  have hsorted := reverseInterlacingRowSchedule_pairwise_ge low mu
  have hprefix_sorted : pref.Pairwise (· ≥ ·) :=
    hsorted.filter (fun i => decide (row ≤ i))
  have hsuffix_sorted : suff.Pairwise (· ≥ ·) :=
    hsorted.filter (fun i => decide (i < row))
  have hsplit_sorted : (pref ++ suff).Pairwise (· ≥ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hprefix_sorted, hsuffix_sorted, ?_⟩
    intro a ha b hb
    exact (le_of_lt (lt_of_mem_adjacentReverseSuffix
      low mu row b hb)).trans
        (le_of_mem_adjacentReversePrefix low mu row a ha)
  exact hperm.symm.eq_of_sortedGE
    (List.sortedGE_iff_pairwise.mpr hsorted)
    (List.sortedGE_iff_pairwise.mpr hsplit_sorted)
end MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
