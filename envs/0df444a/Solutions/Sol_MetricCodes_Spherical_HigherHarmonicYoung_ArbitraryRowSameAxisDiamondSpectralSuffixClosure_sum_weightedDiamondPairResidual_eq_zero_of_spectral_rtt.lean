-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure.sum_weightedDiamondPairResidual_eq_zero_of_spectral_rtt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/539af2a5-17c6-470b-b272-376b6373c8ee

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_pivot_lt_diamondUpperSuffixNext
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_sum_weightedDiamondPairResidual_eq_sum_spectralPrefix_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralSuffixClosure_spectralDiamondPrefixResidual_eq_zero_of_spectral_rtt

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
set_option maxHeartbeats 5000000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTT
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondUniversalPluckerCancellation
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n)
    (hself : ∀ u v : ℝ,
      (spectralPathOperator lam pivot pivot k u).comp
          (spectralPathOperator lam pivot pivot k v) =
        (spectralPathOperator lam pivot pivot k v).comp
          (spectralPathOperator lam pivot pivot k u))
    (hrtt : ∀ (s t : Fin (r + 1)),
      pivot ≤ s → pivot ≤ t → ∀ u v : ℝ,
        (u - v) •
            ((spectralPathOperator lam pivot s k u).comp
                (spectralPathOperator lam pivot t k v) -
              (spectralPathOperator lam pivot t k v).comp
                (spectralPathOperator lam pivot s k u)) =
          (spectralPathOperator lam pivot t k u).comp
              (spectralPathOperator lam pivot s k v) -
            (spectralPathOperator lam pivot t k v).comp
              (spectralPathOperator lam pivot s k u)) :
    (∑ S ∈ ((precedingRows target).erase pivot).powerset,
      polarizationPathCoefficient lam target (insert pivot S) •
        diamondPairResidual lam target pivot k S) = 0 := by
  rw [sum_weightedDiamondPairResidual_eq_sum_spectralPrefix_suffix
    lam hdom target pivot hpivot k]
  simp only [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro U hU
  rw [spectralDiamondPrefixResidual_eq_zero_of_spectral_rtt
    lam target pivot (diamondUpperSuffixNext target U)
      (pivot_lt_diamondUpperSuffixNext target pivot hpivot U
        (Finset.mem_powerset.mp hU)) k hself hrtt]
  simp
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure
