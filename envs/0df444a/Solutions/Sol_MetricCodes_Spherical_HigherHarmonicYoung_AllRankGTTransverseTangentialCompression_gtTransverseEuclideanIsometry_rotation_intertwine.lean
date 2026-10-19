-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression.gtTransverseEuclideanIsometry_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/8ed6df0d-0542-40ee-98b3-6a5629adc6c8

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
    (n : ℕ) (a b : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.comp
        (euclideanAmbientRotation a b) =
      (euclideanAmbientRotation a.castSucc b.castSucc).comp
        (gtTransverseEuclideanIsometry n).toLinearMap := by
  apply LinearMap.ext
  intro v
  ext i
  induction i using Fin.lastCases with
  | last =>
      simp [euclideanAmbientRotation_apply,
        gtTransverseEuclideanIsometry_last,
        EuclideanSpace.basisFun_apply]
  | cast i =>
      simp [euclideanAmbientRotation_apply,
        gtTransverseEuclideanIsometry_castSucc,
        EuclideanSpace.basisFun_apply, PiLp.single_apply]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
