-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.polarizationPathStart_union_eq_lower_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/3015d6d9-c546-41a9-a90b-c9c325faf24c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondResidualSuffixPartition_sort_eq_preceding_append_succeeding
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_precedingDiamondSubset_union
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_succeedingDiamondSubset_union
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_pivot_not_mem_preceding_union_succeeding

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
set_option maxHeartbeats 3000000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
theorem _root_.solution
    {r : ℕ} (target pivot next : Fin (r + 1))
    (L U : Finset (Fin (r + 1))) (tail : List (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot)
    (hupper : (U.sort (· ≤ ·)) ++ [target] = next :: tail) :
    polarizationPathStart target (L ∪ U) =
      polarizationPathStart next L := by
  have hnot := pivot_not_mem_preceding_union_succeeding
    target pivot L U hL hU
  rw [← sort_headD_eq_polarizationPathStart target (L ∪ U),
    sort_eq_preceding_append_succeeding pivot (L ∪ U) hnot,
    precedingDiamondSubset_union target pivot L U hL hU,
    succeedingDiamondSubset_union target pivot L U hL hU,
    ← sort_headD_eq_polarizationPathStart next L]
  cases hlower : L.sort (· ≤ ·) with
  | nil =>
      simp only [List.nil_append, List.headD_nil]
      have hhead :
          (U.sort (· ≤ ·)).headD target =
            ((U.sort (· ≤ ·)) ++ [target]).headD target := by
        cases U.sort (· ≤ ·) <;> rfl
      rw [hhead, hupper]
      rfl
  | cons a rest => simp
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
