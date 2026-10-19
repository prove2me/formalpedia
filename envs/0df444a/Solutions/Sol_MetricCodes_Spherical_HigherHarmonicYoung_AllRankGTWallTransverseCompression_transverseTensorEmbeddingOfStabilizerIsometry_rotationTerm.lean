-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/025f4f51-64db-4317-9eaa-abcc5c41947b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
theorem _root_.solution
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (a b : Fin (n + 1)) :
    (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) =
      TensorProduct.map
        ((gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
          ((euclideanAmbientRotation a b).comp
            (gtTransverseEuclideanIsometry n).toLinearMap))
        (F.toLinearMap.adjoint.comp
          ((youngAmbientRotation lam a b).comp F.toLinearMap)) := by
  change
    (TensorProduct.map
      (gtTransverseEuclideanIsometry n).toLinearMap F.toLinearMap).adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (TensorProduct.map
            (gtTransverseEuclideanIsometry n).toLinearMap F.toLinearMap)) = _
  rw [TensorProduct.adjoint_map]
  apply TensorProduct.ext
  ext v p
  rfl
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
