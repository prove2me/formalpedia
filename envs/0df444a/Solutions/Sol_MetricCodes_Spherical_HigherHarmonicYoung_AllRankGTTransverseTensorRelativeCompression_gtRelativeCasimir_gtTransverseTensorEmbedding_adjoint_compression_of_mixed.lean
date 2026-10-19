-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression.gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/393d8a8f-fa42-4e55-8c59-49b32f676933

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTensorRelativeCompression_gtRelativeCasimir_transverse_compression_of_mixed

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
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (hmixed :
      (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
        gtMixedRotationOperator (n := n) nu) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      gtStabilizerShiftedRelativeCasimir nu := by
  exact gtRelativeCasimir_transverse_compression_of_mixed lam nu
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap
    (gtTransverseTensorEmbedding lam nu h hgram).adjoint_comp_self'
    hmixed
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
