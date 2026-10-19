-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.sum_weightedDiamondPairResidual_eq_sum_spectralPrefix_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/43226ecb-fb3b-4805-8d0f-448409fd8e7b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_upperDiamondSuffix_eq_next_cons_tail
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_sum_spectralLocalDiamondResidual_eq_spectralPrefix
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_diamondPairResidual_union_eq_local_comp_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_sum_weightedDiamondPairResidual_eq_sum_upper_lower

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
          (spectralDiamondPrefixResidual lam target pivot
            (diamondUpperSuffixNext target U) k).comp
              (lowerPolarizationPath
                ((U.sort (· ≤ ·)) ++ [target]))) := by
  classical
  rw [sum_weightedDiamondPairResidual_eq_sum_upper_lower
    lam hdom target pivot hpivot k]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  have hUsub : U ⊆ diamondSucceedingRows target pivot :=
    Finset.mem_powerset.mp hU
  let next := diamondUpperSuffixNext target U
  let tail := diamondUpperSuffixTail target U
  have hupper : (U.sort (· ≤ ·)) ++ [target] = next :: tail :=
    upperDiamondSuffix_eq_next_cons_tail target U
  congr 1
  rw [hupper]
  calc
    (∑ L ∈ (precedingRows pivot).powerset,
      spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
        diamondPairResidual lam target pivot k (L ∪ U)) =
      (∑ L ∈ (precedingRows pivot).powerset,
        spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
          localSpectralDiamondResidual lam target pivot next k L).comp
            (lowerPolarizationPath (next :: tail)) := by
      apply LinearMap.ext
      intro p
      simp only [LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply]
      apply Finset.sum_congr rfl
      intro L hL
      rw [diamondPairResidual_union_eq_local_comp_suffix
        lam target pivot next hpivot k L U tail
          (Finset.mem_powerset.mp hL) hUsub hupper]
      rfl
    _ = (spectralDiamondPrefixResidual lam target pivot next k).comp
          (lowerPolarizationPath (next :: tail)) := by
      rw [sum_spectralLocalDiamondResidual_eq_spectralPrefix
        lam target pivot next k]
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
