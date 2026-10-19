-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondUniversalPluckerCancellation.spectralBooleanPrefixResidual_eq_zero_of_rtt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/e481d433-837b-453e-9414-044fe7a6757f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondUniversalPluckerCancellation
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonHighest
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondUniversalPluckerCancellation
theorem _root_.solution
    {r n : ℕ}
    (A B C D E : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
    (h : ℝ)
    (hcomm : A.comp B = B.comp A)
    (hroot : E.comp B - B.comp E = D)
    (hrtt : (h + 1) • (C.comp B - B.comp C) =
      A.comp D - B.comp C) :
    (((A.comp E).comp B - B.comp (A.comp E)) -
        h • (C.comp B - B.comp C)) - C.comp B = 0 := by
  have htransport :
      (A.comp E).comp B - B.comp (A.comp E) = A.comp D := by
    calc
      (A.comp E).comp B - B.comp (A.comp E) =
          A.comp (E.comp B) - (B.comp A).comp E := by
            simp only [LinearMap.comp_assoc]
      _ = A.comp (E.comp B) - (A.comp B).comp E := by rw [hcomm]
      _ = A.comp (E.comp B - B.comp E) := by
            rw [LinearMap.comp_sub, LinearMap.comp_assoc]
      _ = A.comp D := by rw [hroot]
  rw [htransport]
  have hrelation :
      A.comp D = (h + 1) • (C.comp B - B.comp C) + B.comp C := by
    rw [hrtt]
    module
  rw [hrelation]
  module
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondUniversalPluckerCancellation
