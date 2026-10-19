-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule.reverseInterlacingRowSchedule_raiseWeight_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/ed4df455-4768-42ca-b21c-bd5b506d1e95

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungArbitraryRankAdjacentInterlacingSchedule_interlacingGap_raiseWeight

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
    (reverseInterlacingRowSchedule (raiseWeight low row) mu).count i =
      (reverseInterlacingRowSchedule low mu).count i +
        if i = row then 1 else 0 := by
  rw [reverseInterlacingRowSchedule_count,
    reverseInterlacingRowSchedule_count,
    interlacingGap_raiseWeight hlow row i]
end MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
