-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression.gtTransverseNegativeSector_relativeCasimir_adjoint_compression_of_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/edd8c51a-25c6-470b-bf62-9ae96c451fdf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTStabilizerCasimirShift_gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
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
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (hmixed :
      (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hgram).toLinearMap.adjoint.comp
          ((gtMixedRotationOperator (n := n + 1) lam).comp
            (gtTransverseTensorEmbedding lam (raiseWeight mu row)
              hnu hgram).toLinearMap) =
        gtMixedRotationOperator (n := n) (raiseWeight mu row))
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransverseNegativeSector lam mu row hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, false)) •
          youngClebschRaise (raiseWeight mu row) mu
            (sum_raiseWeight mu row) row p := by
  exact (LinearMap.congr_fun
    (gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed
      lam (raiseWeight mu row) hnu hgram hmixed)
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row p)).trans
    (gtStabilizerShiftedRelativeCasimir_raiseTarget_channel mu row
      (youngClebschRaise (raiseWeight mu row) mu
        (sum_raiseWeight mu row) row)
      (fun a b => youngClebschRaise_rotation_intertwine
        (raiseWeight mu row) mu (sum_raiseWeight mu row) row a b)
      p)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
