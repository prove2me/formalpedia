-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression.gtTransversePositiveSector_relativeCasimir_adjoint_compression_of_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/fcfa3d45-6d7b-485d-a9cc-daff3bcc5dca

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTStabilizerCasimirShift_gtStabilizerShiftedRelativeCasimir_lowerTarget_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTensorRelativeCompression_gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed

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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (hmixed :
      (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap) =
        gtMixedRotationOperator (n := n) nu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransversePositiveSector lam mu nu row hmu hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, true)) •
          youngClebschLower nu mu
            (by rw [hmu]; exact sum_raiseWeight nu row) row p := by
  exact (LinearMap.congr_fun
    (gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed
      lam nu hnu hgram hmixed)
    (youngClebschLower nu mu
      (by rw [hmu]; exact sum_raiseWeight nu row) row p)).trans
    (gtStabilizerShiftedRelativeCasimir_lowerTarget_channel mu nu row hmu
      (youngClebschLower nu mu
        (by rw [hmu]; exact sum_raiseWeight nu row) row)
      (fun a b => youngClebschLower_rotation_intertwine
        nu mu (by rw [hmu]; exact sum_raiseWeight nu row) row a b)
      p)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
