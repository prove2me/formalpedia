-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression.gtTransverseEuclideanIsometry_cross_rotation_compression_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/452a1405-30ba-43b7-b599-b7044ffa2249

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseEuclideanIsometry_adjoint_basisFun_last

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
    (n : ℕ) (a : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
        ((euclideanAmbientRotation (Fin.last n) a.castSucc).comp
          (gtTransverseEuclideanIsometry n).toLinearMap) = 0 := by
  apply LinearMap.ext
  intro v
  change
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
      (euclideanAmbientRotation (Fin.last n) a.castSucc
        (gtTransverseEuclideanIsometry n v)) = 0
  rw [euclideanAmbientRotation_apply,
    gtTransverseEuclideanIsometry_last, zero_smul, sub_zero,
    map_smul,
    gtTransverseEuclideanIsometry_adjoint_basisFun_last,
    smul_zero]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
