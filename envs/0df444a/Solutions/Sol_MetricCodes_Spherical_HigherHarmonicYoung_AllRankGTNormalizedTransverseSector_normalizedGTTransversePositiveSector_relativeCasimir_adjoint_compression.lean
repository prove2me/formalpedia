-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector.normalizedGTTransversePositiveSector_relativeCasimir_adjoint_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/1582133f-ec0a-4515-a19a-9929e277b7c4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTensorRelativeCompression_gtTransversePositiveSector_relativeCasimir_adjoint_compression
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
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu) :
    (normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (normalizedGTTransversePositiveSector lam mu nu row
            hmunu hmu hnu hnuGram).toLinearMap) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift
          (n + 1) mu) (.inr (row, true)) •
          LinearMap.id := by
  apply isometric_scaled_sector_adjoint_compression
    (gtTransverseTensorEmbedding lam nu hnu hnuGram)
    (youngClebschLower nu mu
      (by rw [hmunu]; exact sum_raiseWeight nu row) row)
    (normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram)
    (gtRelativeCasimir lam)
    (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift
        (n + 1) mu) (.inr (row, true)))
  · exact normalizedGTTransversePositiveSector_toLinearMap
      lam mu nu row hmunu hmu hnu hnuGram
  · intro p
    exact gtTransversePositiveSector_relativeCasimir_adjoint_compression
      lam mu nu row hmunu hnu hnuGram p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
