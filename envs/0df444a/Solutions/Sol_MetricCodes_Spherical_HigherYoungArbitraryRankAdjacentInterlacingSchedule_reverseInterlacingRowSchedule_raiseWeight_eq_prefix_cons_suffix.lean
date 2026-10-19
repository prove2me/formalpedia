-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule.reverseInterlacingRowSchedule_raiseWeight_eq_prefix_cons_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/cea75b99-f6d8-4bb8-98bd-44129f8b6e9f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_reverseInterlacingRowSchedule_raiseWeight_perm
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_le_of_mem_adjacentReversePrefix
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_lt_of_mem_adjacentReverseSuffix
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix

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
    {r : ℕ} {low : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (hlow : Interlaces low mu)
    (row : Fin (r + 2)) :
    reverseInterlacingRowSchedule (raiseWeight low row) mu =
      adjacentReversePrefix low mu row ++ row ::
        adjacentReverseSuffix low mu row := by
  classical
  let pref := adjacentReversePrefix low mu row
  let suff := adjacentReverseSuffix low mu row
  have hlowSchedule : reverseInterlacingRowSchedule low mu = pref ++ suff :=
    reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix
      low mu row
  have hperm :
      (reverseInterlacingRowSchedule (raiseWeight low row) mu).Perm
        (pref ++ row :: suff) := by
    have hfirst := reverseInterlacingRowSchedule_raiseWeight_perm hlow row
    rw [hlowSchedule] at hfirst
    have hswap : (pref ++ suff ++ [row]).Perm (pref ++ row :: suff) := by
      simpa [List.append_assoc] using
        (List.perm_append_comm (l₁ := suff) (l₂ := [row])).append_left pref
    exact hfirst.trans hswap
  have hsortedLow := reverseInterlacingRowSchedule_pairwise_ge low mu
  have hprefix_sorted : pref.Pairwise (· ≥ ·) :=
    hsortedLow.filter (fun i => decide (row ≤ i))
  have hsuffix_sorted : suff.Pairwise (· ≥ ·) :=
    hsortedLow.filter (fun i => decide (i < row))
  have hcons_sorted : (row :: suff).Pairwise (· ≥ ·) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, hsuffix_sorted⟩
    intro i hi
    exact le_of_lt (lt_of_mem_adjacentReverseSuffix low mu row i hi)
  have htarget_sorted : (pref ++ row :: suff).Pairwise (· ≥ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hprefix_sorted, hcons_sorted, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with hrow | hb
    · subst b
      exact le_of_mem_adjacentReversePrefix low mu row a ha
    · exact (le_of_lt (lt_of_mem_adjacentReverseSuffix
        low mu row b hb)).trans
          (le_of_mem_adjacentReversePrefix low mu row a ha)
  exact hperm.eq_of_sortedGE
    (List.sortedGE_iff_pairwise.mpr
      (reverseInterlacingRowSchedule_pairwise_ge (raiseWeight low row) mu))
    (List.sortedGE_iff_pairwise.mpr htarget_sorted)
end MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
