-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure.spectralDiamondPrefixResidual_eq_zero_of_spectral_rtt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/5a99a640-5e6e-4494-ab76-fe52c42be0d3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondUniversalPluckerCancellation_spectralPathPrefixResidual_eq_zero_of_rtt

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (hnext : pivot < next)
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
    spectralDiamondPrefixResidual lam target pivot next k = 0 := by
  let h : ℝ := shiftedRowGap lam target pivot
  have hcomm :
      (spectralPathOperator lam pivot pivot k (h + 1)).comp
          (arbitraryRowAxialRaise lam pivot k) =
        (arbitraryRowAxialRaise lam pivot k).comp
          (spectralPathOperator lam pivot pivot k (h + 1)) := by
    simpa only [spectralPathOperator_self_zero] using hself (h + 1) 0
  have hcross :
      (h + 1) •
          ((spectralPathOperator lam pivot next k (h + 1)).comp
              (arbitraryRowAxialRaise lam pivot k) -
            (arbitraryRowAxialRaise lam pivot k).comp
              (spectralPathOperator lam pivot next k (h + 1))) =
        (spectralPathOperator lam pivot pivot k (h + 1)).comp
            (spectralPathOperator lam pivot next k 0) -
          (arbitraryRowAxialRaise lam pivot k).comp
            (spectralPathOperator lam pivot next k (h + 1)) := by
    simpa only [sub_zero, spectralPathOperator_self_zero] using
      hrtt next pivot hnext.le le_rfl (h + 1) 0
  exact spectralPathPrefixResidual_eq_zero_of_rtt
    lam pivot next hnext k h hcomm hcross
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure
