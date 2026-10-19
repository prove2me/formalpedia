-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow.tensor_mapIsometry_range_eq_of_second_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/feb81c1f-a4f1-4d54-a734-4c242b1d90e3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
theorem _root_.solution
    {E F X Y Z : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (e : E →ₗᵢ[ℝ] F) (g : X →ₗᵢ[ℝ] Z) (h : Y →ₗᵢ[ℝ] Z)
    (heq : LinearMap.range g.toLinearMap = LinearMap.range h.toLinearMap) :
    LinearMap.range (TensorProduct.mapIsometry e g).toLinearMap =
      LinearMap.range (TensorProduct.mapIsometry e h).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul v p =>
        have hmem : g p ∈ LinearMap.range h.toLinearMap := by
          rw [← heq]
          exact ⟨p, rfl⟩
        obtain ⟨q, hq⟩ := hmem
        change h q = g p at hq
        refine ⟨v ⊗ₜ[ℝ] q, ?_⟩
        change e v ⊗ₜ[ℝ] h q = e v ⊗ₜ[ℝ] g p
        rw [hq]
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul v p =>
        have hmem : h p ∈ LinearMap.range g.toLinearMap := by
          rw [heq]
          exact ⟨p, rfl⟩
        obtain ⟨q, hq⟩ := hmem
        change g q = h p at hq
        refine ⟨v ⊗ₜ[ℝ] q, ?_⟩
        change e v ⊗ₜ[ℝ] g q = e v ⊗ₜ[ℝ] h p
        rw [hq]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
