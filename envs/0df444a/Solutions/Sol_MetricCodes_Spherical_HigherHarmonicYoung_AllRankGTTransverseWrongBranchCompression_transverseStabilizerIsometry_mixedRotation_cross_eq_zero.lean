-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWrongBranchCompression.transverseStabilizerIsometry_mixedRotation_cross_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/521c077c-683b-422e-848b-15bf8b5ba801

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseEuclideanIsometry_cross_rotation_compression
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseEuclideanIsometry_cross_rotation_compression_swap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseWrongBranchCompression_transverseStabilizerIsometry_rotationTerm_cross
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.gtTransverseWallTensorEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_toLinearMap
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_apply
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition.gtFullTransverseInternalEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition.gtFullAxisEmbedding_apply

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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWrongBranchCompression
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWrongBranchCompression
theorem _root_.solution
    {s t r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (source : Fin (s + 1) → ℕ) (target : Fin (t + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) source →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (G : HarmonicYoungSpace (n := n) target →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (horth : F.toLinearMap.adjoint.comp G.toLinearMap = 0)
    (hG : ∀ a b : Fin n,
      G.toLinearMap.comp (youngAmbientRotation target a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp G.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry
      lam source F).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0 := by
  let I := (transverseTensorEmbeddingOfStabilizerIsometry
    lam source F).toLinearMap
  let J := (transverseTensorEmbeddingOfStabilizerIsometry
    lam target G).toLinearMap
  have htangential (a b : Fin n) :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc b.castSucc)
          (youngAmbientRotation lam a.castSucc b.castSucc)).comp J) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc b.castSucc)
          (youngAmbientRotation lam a.castSucc b.castSucc)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross]
    have hz : F.toLinearMap.adjoint.comp
        ((youngAmbientRotation lam a.castSucc b.castSucc).comp G.toLinearMap) = 0 := by
      rw [← hG a b, ← LinearMap.comp_assoc, horth, LinearMap.zero_comp]
    rw [hz]
    apply TensorProduct.ext
    ext v p
    simp
  have hcross (a : Fin n) :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc (Fin.last n))
          (youngAmbientRotation lam a.castSucc (Fin.last n))).comp J) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc (Fin.last n))
          (youngAmbientRotation lam a.castSucc (Fin.last n))).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross,
      gtTransverseEuclideanIsometry_cross_rotation_compression]
    apply TensorProduct.ext
    ext v p
    simp
  have hcrossSwap (a : Fin n) :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) a.castSucc)
          (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp J) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) a.castSucc)
          (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross,
      gtTransverseEuclideanIsometry_cross_rotation_compression_swap]
    apply TensorProduct.ext
    ext v p
    simp
  have hlast :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) (Fin.last n))
          (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp J) = 0 := by
    have hzero : euclideanAmbientRotation (Fin.last n) (Fin.last n) = 0 := by
      apply LinearMap.ext
      intro v
      simp [euclideanAmbientRotation_apply]
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) (Fin.last n))
          (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross, hzero]
    simp
  unfold gtMixedRotationOperator
  change I.adjoint.comp ((∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
    TensorProduct.map (euclideanAmbientRotation a b)
      (youngAmbientRotation lam a b)).comp J) = 0
  apply TensorProduct.ext'
  intro v p
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    LinearMap.zero_apply]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have htangential' (a b : Fin n) :=
    LinearMap.congr_fun (htangential a b) (v ⊗ₜ[ℝ] p)
  have hcross' (a : Fin n) :=
    LinearMap.congr_fun (hcross a) (v ⊗ₜ[ℝ] p)
  have hcrossSwap' (a : Fin n) :=
    LinearMap.congr_fun (hcrossSwap a) (v ⊗ₜ[ℝ] p)
  have hlast' := LinearMap.congr_fun hlast (v ⊗ₜ[ℝ] p)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    at htangential' hcross' hcrossSwap' hlast'
  simp only [htangential', hcross', hcrossSwap', hlast',
    Finset.sum_const_zero, add_zero]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWrongBranchCompression
