-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.transverseTensorEmbeddingOfStabilizerIsometry_relativeCasimir
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/721b0689-8c36-45ac-9e4b-6d25d2e1eb9a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTensorRelativeCompression_gtRelativeCasimir_eq_scalar_sub_mixed
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_transverseTensorEmbeddingOfStabilizerIsometry_mixedRotation

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
    (hF : ∀ a b : Fin n,
      F.toLinearMap.comp (youngAmbientRotation nu a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) =
      gtStabilizerShiftedRelativeCasimir nu := by
  rw [gtRelativeCasimir_eq_scalar_sub_mixed (n := n + 1) lam,
    gtStabilizerShiftedRelativeCasimir,
    gtRelativeCasimir_eq_scalar_sub_mixed (n := n) nu]
  simp only [LinearMap.sub_comp, LinearMap.smul_comp,
    LinearMap.id_comp, LinearMap.comp_sub, LinearMap.comp_smul]
  rw [(transverseTensorEmbeddingOfStabilizerIsometry
    lam nu F).adjoint_comp_self',
    transverseTensorEmbeddingOfStabilizerIsometry_mixedRotation
      lam nu F hF]
  norm_num
  module
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
