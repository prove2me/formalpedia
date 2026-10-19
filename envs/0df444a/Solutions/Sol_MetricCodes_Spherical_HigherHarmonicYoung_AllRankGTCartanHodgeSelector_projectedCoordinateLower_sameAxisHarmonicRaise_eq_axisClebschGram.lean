-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector.projectedCoordinateLower_sameAxisHarmonicRaise_eq_axisClebschGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/cbbd915a-8e48-4316-bf86-d22eb827b7f3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanHodgeSelector_youngClebschLower_adjoint_comp_gtYoungAxisTensor
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanHodgeSelector_gtYoungAxisTensor_adjoint_comp_youngClebschLower
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanHodgeSelector_arbitraryRowSameAxisHarmonicRaise_eq_lowerScalar_smul_projectedCoordinateRaise

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
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 700000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.UniversalBGGRootComplex
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
theorem _root_.solution
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (hdom : Antitone low)
    (row : Fin (r + 1)) (k : Fin n)
    (p : HarmonicYoungSpace (n := n) low) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin n) ℝ k)
        (arbitraryRowSameAxisHarmonicRaise low hdom row k p) =
      arbitraryRowAxialLowerScalar low row •
        (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k)).adjoint
          (((youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row).comp
            (youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row).adjoint)
            (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k) p)) := by
  rw [arbitraryRowSameAxisHarmonicRaise_eq_lowerScalar_smul_projectedCoordinateRaise,
    map_smul]
  congr 1
  have hlower := LinearMap.congr_fun
    (gtYoungAxisTensor_adjoint_comp_youngClebschLower
      low (raiseWeight low row) (sum_raiseWeight low row) row
      (EuclideanSpace.basisFun (Fin n) ℝ k))
    (projectedCoordinateRaise (raiseWeight low row) low
      (sum_raiseWeight low row) row
      (EuclideanSpace.basisFun (Fin n) ℝ k) p)
  have hraise := LinearMap.congr_fun
    (youngClebschLower_adjoint_comp_gtYoungAxisTensor
      low (raiseWeight low row) (sum_raiseWeight low row) row
      (EuclideanSpace.basisFun (Fin n) ℝ k)) p
  simp only [LinearMap.comp_apply] at hraise
  simp only [LinearMap.comp_apply]
  rw [hraise]
  simpa only [LinearMap.comp_apply] using hlower.symm
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
