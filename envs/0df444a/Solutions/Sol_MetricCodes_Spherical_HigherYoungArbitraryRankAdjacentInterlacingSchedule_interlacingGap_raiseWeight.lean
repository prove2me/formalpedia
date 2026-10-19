-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule.interlacingGap_raiseWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/4a30e7d6-a175-4b30-b139-6d554b016372

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (row i : Fin (r + 2)) :
    interlacingGap (raiseWeight low row) mu i =
      interlacingGap low mu i + if i = row then 1 else 0 := by
  classical
  by_cases hi : i = row
  · subst i
    have hbase := appendZeroWeight_le_of_interlaces hlow row
    simp only [interlacingGap, raiseWeight, Function.update_self,
      if_true]
    omega
  · have hri : row ≠ i := Ne.symm hi
    simp [interlacingGap, raiseWeight, hi]
end MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
