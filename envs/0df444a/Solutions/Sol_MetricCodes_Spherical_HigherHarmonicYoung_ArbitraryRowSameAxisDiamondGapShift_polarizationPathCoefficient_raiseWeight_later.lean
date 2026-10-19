-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift.polarizationPathCoefficient_raiseWeight_later
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/184b3518-8948-432c-b12b-4267dd9749e9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondGapShift_shiftedRowGap_raiseWeight_later

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
    (target raised : Fin (r + 1)) (htarget : target < raised)
    (S : Finset (Fin (r + 1))) :
    polarizationPathCoefficient (raiseWeight lam raised) target S =
      polarizationPathCoefficient lam target S := by
  classical
  unfold polarizationPathCoefficient
  congr 1
  apply Finset.prod_congr rfl
  intro preceding hpreceding
  apply shiftedRowGap_raiseWeight_later lam target raised preceding htarget
  exact (mem_precedingRows preceding target).mp
    (Finset.mem_sdiff.mp hpreceding).1
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift
