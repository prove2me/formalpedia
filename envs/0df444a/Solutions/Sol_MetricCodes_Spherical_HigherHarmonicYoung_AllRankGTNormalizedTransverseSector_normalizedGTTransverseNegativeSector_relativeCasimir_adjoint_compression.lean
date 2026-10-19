-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector.normalizedGTTransverseNegativeSector_relativeCasimir_adjoint_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/2a05773b-3a3b-4040-9512-1109ee48f1a6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTensorRelativeCompression_gtTransverseNegativeSector_relativeCasimir_adjoint_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTNormalizedTransverseSector_isometric_scaled_sector_adjoint_compression

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
set_option maxHeartbeats 3000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa) :
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (normalizedGTTransverseNegativeSector lam mu kappa row
            hnu hnuGram hfinite hraise).toLinearMap) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift
          (n + 1) mu) (.inr (row, false)) •
          LinearMap.id := by
  apply isometric_scaled_sector_adjoint_compression
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram)
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row)
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise)
    (gtRelativeCasimir lam)
    (Real.sqrt (internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row))⁻¹
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift
        (n + 1) mu) (.inr (row, false)))
  · exact normalizedGTTransverseNegativeSector_toLinearMap
      lam mu kappa row hnu hnuGram hfinite hraise
  · intro p
    exact gtTransverseNegativeSector_relativeCasimir_adjoint_compression
      lam mu row hnu hnuGram p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
