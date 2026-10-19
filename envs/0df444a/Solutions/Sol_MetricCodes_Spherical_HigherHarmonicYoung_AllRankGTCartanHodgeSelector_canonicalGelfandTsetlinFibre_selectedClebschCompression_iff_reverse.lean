-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector.canonicalGelfandTsetlinFibre_selectedClebschCompression_iff_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/19480370-698b-4720-847a-9561961af36d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGelfandTsetlinCanonicalFibre_canonicalGelfandTsetlinFibre_phase_pos

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
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hlow : Interlaces low mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (row : Fin (r + 2)) (p : HarmonicYoungSpace (n := n) mu) :
    (gtYoungAxisTensor low
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).adjoint
        (gtSelectedRowClebschRangeProjector low row
          (gtYoungAxisTensor low
            (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
              (canonicalGelfandTsetlinFibre low mu hlow hgram p))) =
      plusProbability (n + 1) low mu row •
        canonicalGelfandTsetlinFibre low mu hlow hgram p ↔
    (gtYoungAxisTensor low
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).adjoint
        (gtSelectedRowClebschRangeProjector low row
          (gtYoungAxisTensor low
            (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
              (reverseInterlacingHarmonicBranch low mu hlow p))) =
      plusProbability (n + 1) low mu row •
        reverseInterlacingHarmonicBranch low mu hlow p := by
  have hscalar := (canonicalGelfandTsetlinFibre_phase_pos
    low mu hlow hgram).ne'
  simp only [canonicalGelfandTsetlinFibre_apply, map_smul, smul_smul]
  rw [mul_comm (plusProbability (n + 1) low mu row), mul_smul,
    smul_right_inj hscalar]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
