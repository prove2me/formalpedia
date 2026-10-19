-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.diamondPairResidual_union_eq_local_comp_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/c5b1a4f7-ed96-4132-937e-9e7398975077

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondResidualSuffixPartition_sort_eq_preceding_append_succeeding
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondResidualSuffixPartition_sort_insert_eq_preceding_cons_succeeding
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondResidualSuffixPartition_diamondPairResidual_eq_prefix_comp_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_precedingDiamondSubset_union
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_succeedingDiamondSubset_union
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_pivot_not_mem_preceding_union_succeeding
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_omittedDiamondPrefix_union_eq_lowerPath
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_insertedDiamondPrefix_union_eq_lowerPath_comp_root

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n) (L U : Finset (Fin (r + 1)))
    (tail : List (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot)
    (hupper : (U.sort (· ≤ ·)) ++ [target] = next :: tail) :
    diamondPairResidual lam target pivot k (L ∪ U) =
      (localSpectralDiamondResidual lam target pivot next k L).comp
        (lowerPolarizationPath (next :: tail)) := by
  have hnot := pivot_not_mem_preceding_union_succeeding
    target pivot L U hL hU
  have hsorted :
      ((L ∪ U).sort (· ≤ ·)) ++ [target] =
        (L.sort (· ≤ ·)) ++ next :: tail := by
    rw [sort_eq_preceding_append_succeeding pivot (L ∪ U) hnot,
      precedingDiamondSubset_union target pivot L U hL hU,
      succeedingDiamondSubset_union target pivot L U hL hU,
      List.append_assoc, hupper]
  have hinsert :
      ((insert pivot (L ∪ U)).sort (· ≤ ·)) ++ [target] =
        (L.sort (· ≤ ·)) ++ pivot :: next :: tail := by
    rw [sort_insert_eq_preceding_cons_succeeding
      pivot (L ∪ U) hnot,
      precedingDiamondSubset_union target pivot L U hL hU,
      succeedingDiamondSubset_union target pivot L U hL hU,
      List.append_assoc]
    simp only [List.cons_append]
    rw [hupper]
  have hnext : pivot < next := by
    have hmem : next ∈ (U.sort (· ≤ ·)) ++ [target] := by
      rw [hupper]
      simp
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact ((mem_diamondSucceedingRows target pivot next).mp
        (hU ((Finset.mem_sort (· ≤ ·)).mp hmem))).2
    · have hnexttarget : next = target := by simpa using hmem
      simpa [hnexttarget] using hpivot
  have htail : ∀ a ∈ tail, pivot < a := by
    intro a ha
    have hmem : a ∈ (U.sort (· ≤ ·)) ++ [target] := by
      rw [hupper]
      simp [ha]
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact ((mem_diamondSucceedingRows target pivot a).mp
        (hU ((Finset.mem_sort (· ≤ ·)).mp hmem))).2
    · have hatarget : a = target := by simpa using hmem
      simpa [hatarget] using hpivot
  rw [diamondPairResidual_eq_prefix_comp_suffix
    lam target pivot hpivot k (L ∪ U) (L.sort (· ≤ ·)) next tail
      hsorted hinsert hnext htail]
  unfold diamondPrefixResidual localSpectralDiamondResidual
  rw [omittedDiamondPrefix_union_eq_lowerPath
    target pivot next k L U tail hL hU hupper,
    insertedDiamondPrefix_union_eq_lowerPath_comp_root
      target pivot next k L U hL hU]
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
