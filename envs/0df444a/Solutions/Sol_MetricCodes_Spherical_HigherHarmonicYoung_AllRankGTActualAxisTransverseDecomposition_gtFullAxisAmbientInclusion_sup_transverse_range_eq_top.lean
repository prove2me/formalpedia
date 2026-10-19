-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition.gtFullAxisAmbientInclusion_sup_transverse_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/f8d5efec-af60-4bb8-a87c-7955765011b5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_euclidean_eq_gtTransverse_add_last_axis
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.gtTransverseWallTensorEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_toLinearMap
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_apply
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition.gtFullTransverseInternalEmbedding_tmul

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
set_option maxHeartbeats 1200000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    LinearMap.range (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap ⊔
        LinearMap.range
          (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam)) := by
  apply top_unique
  intro x _
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul v p =>
      let w : SpherePacking.Euclidean n :=
        WithLp.toLp 2 (fun i : Fin n => v i.castSucc)
      have hv := euclidean_eq_gtTransverse_add_last_axis v
      change v ⊗ₜ[ℝ] p ∈ _
      rw [hv, TensorProduct.add_tmul]
      apply Submodule.add_mem
      · apply Submodule.mem_sup_right
        exact ⟨w ⊗ₜ[ℝ] p, rfl⟩
      · apply Submodule.mem_sup_left
        refine ⟨v (Fin.last n) • p, ?_⟩
        change
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
              (v (Fin.last n) • p) =
            (v (Fin.last n) •
              (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))) ⊗ₜ[ℝ] p
        simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul]
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
