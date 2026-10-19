-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression.gtTransverseTensorEmbedding_tangentialTerm_adjoint_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/1c680f41-d657-4670-8bb3-11e2e79960df

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_canonicalGelfandTsetlinFibre_rotation_adjoint_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseEuclideanIsometry_rotation_adjoint_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseTensorEmbedding_rotationTerm_adjoint_compression

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
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc b.castSucc)
          (youngAmbientRotation lam a.castSucc b.castSucc)).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      TensorProduct.map (euclideanAmbientRotation a b)
        (youngAmbientRotation nu a b) := by
  rw [gtTransverseTensorEmbedding_rotationTerm_adjoint_compression,
    gtTransverseEuclideanIsometry_rotation_adjoint_compression,
    canonicalGelfandTsetlinFibre_rotation_adjoint_compression]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
