-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector.projectedCoordinateLower_sameAxisHarmonicRaise_eq_plusProbability_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/941e7a70-95a3-454d-a375-e371611c625a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanHodgeSelector_internalRowLowerGramScalar_raiseWeight_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanHodgeSelector_projectedCoordinateLower_sameAxisHarmonicRaise_eq_selectedClebschProjector_compression

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
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (hdom : Antitone low) (row : Fin (r + 1)) (k : Fin n)
    (p : HarmonicYoungSpace (n := n) low) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin n) ℝ k)
        (arbitraryRowSameAxisHarmonicRaise low hdom row k p) =
      (arbitraryRowAxialLowerScalar low row *
        internalRowLowerGramScalar (raiseWeight low row) row *
        plusProbability n low mu row) • p ↔
      (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k)).adjoint
          (gtSelectedRowClebschRangeProjector low row
            (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k) p)) =
        plusProbability n low mu row • p := by
  rw [projectedCoordinateLower_sameAxisHarmonicRaise_eq_selectedClebschProjector_compression]
  have hnonzero :
      arbitraryRowAxialLowerScalar low row *
        internalRowLowerGramScalar (raiseWeight low row) row ≠ 0 :=
    mul_ne_zero (arbitraryRowAxialLowerScalar_pos low row).ne'
      (internalRowLowerGramScalar_raiseWeight_pos low hdom row).ne'
  constructor
  · intro h
    apply smul_right_injective (HarmonicYoungSpace (n := n) low) hnonzero
    simpa [mul_smul] using h
  · intro h
    rw [h, smul_smul]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
