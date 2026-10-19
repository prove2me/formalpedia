-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift.polarizationPathCoefficient_raiseWeight_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/1d72225c-25d3-4769-9b98-bc5c811251ac

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondGapShift_shiftedRowGap_raiseWeight_preceding
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondGapShift_polarizationPathCoefficient_raiseWeight_of_mem

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
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift
theorem _root_.solution
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (hrow : raised < target)
    (hdom : lam target ≤ lam raised)
    (S : Finset (Fin (r + 1))) (hS : raised ∉ S) :
    polarizationPathCoefficient (raiseWeight lam raised) target S =
      polarizationPathCoefficient lam target S -
        polarizationPathCoefficient lam target (insert raised S) := by
  rw [polarizationPathCoefficient_insert
    (raiseWeight lam raised) target raised S hrow hS,
    shiftedRowGap_raiseWeight_preceding lam target raised
      (ne_of_gt hrow) hdom,
    polarizationPathCoefficient_raiseWeight_of_mem lam target raised
      (ne_of_gt hrow) (insert raised S) (Finset.mem_insert_self _ _),
    polarizationPathCoefficient_insert lam target raised S hrow hS]
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift
