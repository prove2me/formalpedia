-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.sum_weightedDiamondPairResidual_eq_sum_upper_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/3c168c80-d2a7-4c6d-87fb-1edd726ef80a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_sum_powerset_disjoint_union
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_precedingRows_erase_pivot_eq_union
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_precedingRows_disjoint_diamondSucceedingRows
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_polarizationPathCoefficient_insert_union_factor

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n) :
    (∑ S ∈ ((precedingRows target).erase pivot).powerset,
      polarizationPathCoefficient lam target (insert pivot S) •
        diamondPairResidual lam target pivot k S) =
      -(∑ U ∈ (diamondSucceedingRows target pivot).powerset,
        upperDiamondPathCoefficient lam target pivot U •
          (∑ L ∈ (precedingRows pivot).powerset,
            spectralPathCoeff lam pivot
              (shiftedRowGap lam target pivot + 1) L •
                diamondPairResidual lam target pivot k (L ∪ U))) := by
  classical
  rw [precedingRows_erase_pivot_eq_union target pivot hpivot,
    sum_powerset_disjoint_union (precedingRows pivot)
      (diamondSucceedingRows target pivot)
      (precedingRows_disjoint_diamondSucceedingRows target pivot)]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  have hUsub : U ⊆ diamondSucceedingRows target pivot :=
    Finset.mem_powerset.mp hU
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro L hL
  rw [polarizationPathCoefficient_insert_union_factor
    lam hdom target pivot hpivot L U
      (Finset.mem_powerset.mp hL) hUsub]
  module
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
