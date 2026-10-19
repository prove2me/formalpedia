-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondUniversalPluckerCancellation.spectralPathPrefixResidual_eq_zero_of_rtt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/91c96c57-2a61-45cc-8635-397371a8da63

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRootTransport_polarization_comp_arbitraryRowAxialRaise_sub
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondUniversalPluckerCancellation_spectralBooleanPrefixResidual_eq_zero_of_rtt

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (pivot next : Fin (r + 1)) (hpivot : pivot < next)
    (k : Fin n) (h : ℝ)
    (hcomm :
      (spectralPathOperator lam pivot pivot k (h + 1)).comp
          (arbitraryRowAxialRaise lam pivot k) =
        (arbitraryRowAxialRaise lam pivot k).comp
          (spectralPathOperator lam pivot pivot k (h + 1)))
    (hrtt :
      (h + 1) •
          ((spectralPathOperator lam pivot next k (h + 1)).comp
              (arbitraryRowAxialRaise lam pivot k) -
            (arbitraryRowAxialRaise lam pivot k).comp
              (spectralPathOperator lam pivot next k (h + 1))) =
        (spectralPathOperator lam pivot pivot k (h + 1)).comp
            (spectralPathOperator lam pivot next k 0) -
          (arbitraryRowAxialRaise lam pivot k).comp
            (spectralPathOperator lam pivot next k (h + 1))) :
    ((((spectralPathOperator lam pivot pivot k (h + 1)).comp
            (polarization r n next pivot)).comp
          (arbitraryRowAxialRaise lam pivot k) -
        (arbitraryRowAxialRaise lam pivot k).comp
          ((spectralPathOperator lam pivot pivot k (h + 1)).comp
            (polarization r n next pivot))) -
      h •
        ((spectralPathOperator lam pivot next k (h + 1)).comp
            (arbitraryRowAxialRaise lam pivot k) -
          (arbitraryRowAxialRaise lam pivot k).comp
            (spectralPathOperator lam pivot next k (h + 1)))) -
      (spectralPathOperator lam pivot next k (h + 1)).comp
        (arbitraryRowAxialRaise lam pivot k) = 0 := by
  exact spectralBooleanPrefixResidual_eq_zero_of_rtt
    (spectralPathOperator lam pivot pivot k (h + 1))
    (arbitraryRowAxialRaise lam pivot k)
    (spectralPathOperator lam pivot next k (h + 1))
    (spectralPathOperator lam pivot next k 0)
    (polarization r n next pivot) h hcomm
    (polarization_comp_arbitraryRowAxialRaise_sub lam pivot next hpivot k)
    hrtt
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondUniversalPluckerCancellation
