-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.polarizationPathCoefficient_insert_union_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/4d48bde0-b2e8-49ce-829d-452d740e6c79

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixCoefficientFactor_polarizationPathCoefficient_insert_pivot_factor
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
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (L U : Finset (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot) :
    polarizationPathCoefficient lam target (insert pivot (L ∪ U)) =
      -upperDiamondPathCoefficient lam target pivot U *
        spectralPathCoeff lam pivot
          (shiftedRowGap lam target pivot + 1) L := by
  rw [polarizationPathCoefficient_insert_pivot_factor
    lam hdom target pivot hpivot (L ∪ U)
      (pivot_not_mem_preceding_union_succeeding
        target pivot L U hL hU),
    precedingDiamondSubset_union target pivot L U hL hU]
  congr 2
  unfold upperDiamondPathCoefficient
  have hupper : succeedingDiamondSubset pivot (L ∪ U) = U :=
    succeedingDiamondSubset_union target pivot L U hL hU
  have hself : succeedingDiamondSubset pivot U = U := by
    ext a
    simp only [succeedingDiamondSubset, Finset.mem_filter]
    constructor
    · exact And.left
    · intro ha
      exact ⟨ha,
        ((mem_diamondSucceedingRows target pivot a).mp (hU ha)).2⟩
  rw [hupper, hself]
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
