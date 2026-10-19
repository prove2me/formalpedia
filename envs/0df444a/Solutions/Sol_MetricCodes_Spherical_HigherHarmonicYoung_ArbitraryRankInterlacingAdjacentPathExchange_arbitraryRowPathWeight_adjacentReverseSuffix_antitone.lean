-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange.arbitraryRowPathWeight_adjacentReverseSuffix_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/acea894c-c766-46fa-a7e5-44f641b8d874

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_arbitraryRowPathWeight_append

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
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamond
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
theorem _root_.solution
    {r : ℕ} {low : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ} (hlow : Interlaces low mu)
    (row : Fin (r + 2))
    (front : List (Fin (r + 2)))
    (hfront : ∀ i,
      front.count i ≤ (adjacentReverseSuffix low mu row).count i) :
    Antitone
      (arbitraryRowPathWeight
        (arbitraryRowPathWeight (appendZeroWeight mu)
          (adjacentReversePrefix low mu row)) front) := by
  have hcount : ∀ i,
      (adjacentReversePrefix low mu row ++ front).count i ≤
        interlacingGap low mu i := by
    intro i
    have hlowcount :
        (adjacentReversePrefix low mu row ++
          adjacentReverseSuffix low mu row).count i =
            interlacingGap low mu i := by
      rw [← reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix,
        reverseInterlacingRowSchedule_count]
    simp only [List.count_append] at hlowcount ⊢
    have hfronti := hfront i
    omega
  have hinterlaces := foldl_interlaces_of_count_le_gap hlow
    (adjacentReversePrefix low mu row ++ front) hcount
  rw [← arbitraryRowPathWeight_eq_foldl,
    arbitraryRowPathWeight_append] at hinterlaces
  exact hinterlaces.antitone_ambient
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
