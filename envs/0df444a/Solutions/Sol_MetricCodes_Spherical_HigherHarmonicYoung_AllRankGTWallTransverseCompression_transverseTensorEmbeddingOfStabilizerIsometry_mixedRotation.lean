-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.transverseTensorEmbeddingOfStabilizerIsometry_mixedRotation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/236174b6-fbfc-433f-80c0-19290549c593

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseEuclideanIsometry_rotation_adjoint_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseEuclideanIsometry_cross_rotation_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseEuclideanIsometry_cross_rotation_compression_swap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_stabilizerIsometry_rotation_adjoint_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm

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
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) =
      gtMixedRotationOperator (n := n) nu := by
  let I := (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap
  have htangential (a b : Fin n) :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc b.castSucc)
            (youngAmbientRotation lam a.castSucc b.castSucc)).comp I) =
        TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation nu a b) := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc b.castSucc)
            (youngAmbientRotation lam a.castSucc b.castSucc)).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = _
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm,
      gtTransverseEuclideanIsometry_rotation_adjoint_compression,
      stabilizerIsometry_rotation_adjoint_compression lam nu F hF]
  have hcross (a : Fin n) :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc (Fin.last n))
            (youngAmbientRotation lam a.castSucc (Fin.last n))).comp I) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc (Fin.last n))
            (youngAmbientRotation lam a.castSucc (Fin.last n))).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = 0
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm,
      gtTransverseEuclideanIsometry_cross_rotation_compression]
    apply TensorProduct.ext
    ext v p
    simp
  have hcrossSwap (a : Fin n) :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) a.castSucc)
            (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp I) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) a.castSucc)
            (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = 0
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm,
      gtTransverseEuclideanIsometry_cross_rotation_compression_swap]
    apply TensorProduct.ext
    ext v p
    simp
  have hlast :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) (Fin.last n))
            (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp I) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) (Fin.last n))
            (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = 0
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm]
    have hzero : euclideanAmbientRotation (Fin.last n) (Fin.last n) = 0 := by
      apply LinearMap.ext
      intro v
      simp [euclideanAmbientRotation_apply]
    rw [hzero]
    simp
  unfold gtMixedRotationOperator
  change I.adjoint.comp ((∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
    TensorProduct.map (euclideanAmbientRotation a b)
      (youngAmbientRotation lam a b)).comp I) = _
  apply TensorProduct.ext'
  intro v p
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have htangential' (a b : Fin n) :=
    LinearMap.congr_fun (htangential a b) (v ⊗ₜ[ℝ] p)
  have hcross' (a : Fin n) :=
    LinearMap.congr_fun (hcross a) (v ⊗ₜ[ℝ] p)
  have hcrossSwap' (a : Fin n) :=
    LinearMap.congr_fun (hcrossSwap a) (v ⊗ₜ[ℝ] p)
  have hlast' := LinearMap.congr_fun hlast (v ⊗ₜ[ℝ] p)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at htangential' hcross' hcrossSwap' hlast'
  simp only [htangential', hcross', hcrossSwap', hlast',
    Finset.sum_const_zero, add_zero]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
