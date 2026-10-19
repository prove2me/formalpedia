-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange.reverseInterlacingPolynomialSeed_adjacent_raise_of_rowDiamond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/88b6138e-6125-4440-8932-1b3dfd5d10a1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowMickelssonGramIdeal_iteratedArbitraryRowAxialRaise_append
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_lt_of_mem_adjacentReverseSuffix
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_reverseInterlacingRowSchedule_raiseWeight_eq_prefix_cons_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_arbitraryRowPathWeight_append
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_arbitraryRowPathWeight_adjacentReversePrefix_append_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankInterlacingAdjacentPathExchange_iteratedArbitraryRowAxialRaise_move_last_of_rowDiamond
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankInterlacingAdjacentPathExchange_arbitraryRowPathWeight_adjacentReverseSuffix_antitone

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
    {r n : ℕ}
    {low : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (hlow : Interlaces low mu) (row : Fin (r + 2))
    (hdiamond : DominantSameAxisRowDiamond (n + 1) row)
    (p : HarmonicYoungSpace (n := n) mu) :
    arbitraryRowAxialRaise low row (Fin.last n)
        (reverseInterlacingPolynomialSeed low mu p) =
      reverseInterlacingPolynomialSeed (raiseWeight low row) mu p := by
  let pref := adjacentReversePrefix low mu row
  let suff := adjacentReverseSuffix low mu row
  let theta := arbitraryRowPathWeight (appendZeroWeight mu) pref
  let z : PolynomialSpace (r + 1) (n + 1) :=
    ((terminalZeroSelectedBranchIsometry mu p :
      HarmonicYoungSpace (n := n + 1) (appendZeroWeight mu)) :
      PolynomialSpace (r + 1) (n + 1))
  have hlowpath : arbitraryRowPathWeight theta suff = low := by
    simpa [theta, pref, suff, arbitraryRowPathWeight_append] using
      arbitraryRowPathWeight_adjacentReversePrefix_append_suffix hlow row
  have hsplitlow :
      reverseInterlacingRowSchedule low mu = pref ++ suff :=
    reverseInterlacingRowSchedule_eq_adjacentReversePrefix_append_suffix
      low mu row
  have hsplithigh :
      reverseInterlacingRowSchedule (raiseWeight low row) mu =
        pref ++ row :: suff :=
    reverseInterlacingRowSchedule_raiseWeight_eq_prefix_cons_suffix hlow row
  change
    arbitraryRowAxialRaise low row (Fin.last n)
        (iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
          (Fin.last n) (reverseInterlacingRowSchedule low mu) z) =
      iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
          (Fin.last n)
          (reverseInterlacingRowSchedule (raiseWeight low row) mu) z
  rw [hsplitlow, hsplithigh,
    iteratedArbitraryRowAxialRaise_append,
    iteratedArbitraryRowAxialRaise_append]
  change
    arbitraryRowAxialRaise low row (Fin.last n)
      (iteratedArbitraryRowAxialRaise theta (Fin.last n) suff
        (iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
          (Fin.last n) pref z)) =
      iteratedArbitraryRowAxialRaise (raiseWeight theta row)
        (Fin.last n) suff
          (arbitraryRowAxialRaise theta row (Fin.last n)
            (iteratedArbitraryRowAxialRaise (appendZeroWeight mu)
              (Fin.last n) pref z))
  rw [← hlowpath]
  apply iteratedArbitraryRowAxialRaise_move_last_of_rowDiamond
    theta suff row hdiamond
  · intro i hi
    exact lt_of_mem_adjacentReverseSuffix low mu row i hi
  · intro t ht
    exact arbitraryRowPathWeight_adjacentReverseSuffix_antitone
      hlow row t ht
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
