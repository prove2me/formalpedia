-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection.gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/b4b7f67c-b396-4029-84a5-a97c11d5fdc3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalSelectedBranchRange_canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch

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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (tau : Fin (r + 1) → ℕ) (h : Interlaces lam tau)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hdom : Antitone lam)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam tau h) :
    LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces tau h)).toLinearMap =
      LinearMap.range
        (gtTransverseTensorEmbedding lam tau h hgram).toLinearMap := by
  change
    LinearMap.range
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          (canonicalFullBranchFibre lam hn
            (fullBranchOfInterlaces tau h)).toLinearMap) =
      LinearMap.range
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          (canonicalGelfandTsetlinFibre lam tau h hgram).toLinearMap)
  rw [TensorProduct.range_map, TensorProduct.range_map,
    canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
      lam tau h hn hdom hgram]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection
