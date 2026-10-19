-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalRetainedAdditiveColumn.linearMap_comp_eq_smul_add_of_complete_adjoint_block_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/0b339f00-21a8-4610-ae46-563c28dc60bf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalCompleteBlockReconstruction_eq_of_iSup_range_sup_eq_top_of_adjoint_eq
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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalRetainedAdditiveColumn
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalRetainedAdditiveColumn
theorem _root_.solution
    {ι κ E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (X : ι → Type*) (Y : κ → Type*)
    [∀ i, NormedAddCommGroup (X i)]
    [∀ i, InnerProductSpace ℝ (X i)]
    [∀ i, FiniteDimensional ℝ (X i)]
    [∀ j, NormedAddCommGroup (Y j)]
    [∀ j, InnerProductSpace ℝ (Y j)]
    [∀ j, FiniteDimensional ℝ (Y j)]
    (C : (i : ι) → X i →ₗ[ℝ] V)
    (D : (j : κ) → Y j →ₗ[ℝ] V)
    (hcomplete :
      (⨆ i : ι, LinearMap.range (C i)) ⊔
        (⨆ j : κ, LinearMap.range (D j)) = ⊤)
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (A : F →ₗ[ℝ] V)
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (haxis : ∀ i : ι,
      (C i).adjoint.comp (T.comp B) =
        d • ((C i).adjoint.comp B) +
          ((C i).adjoint.comp A).comp K)
    (htransverse : ∀ j : κ,
      (D j).adjoint.comp (T.comp B) =
        d • ((D j).adjoint.comp B) +
          ((D j).adjoint.comp A).comp K) :
    T.comp B = d • B + A.comp K := by
  apply LinearMap.ext
  intro p
  apply eq_of_iSup_range_sup_eq_top_of_adjoint_eq
    X Y C D hcomplete (T (B p)) (d • B p + A (K p))
  · intro i
    have hi := LinearMap.congr_fun (haxis i) p
    simpa only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul] using hi
  · intro j
    have hj := LinearMap.congr_fun (htransverse j) p
    simpa only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul] using hj
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalRetainedAdditiveColumn
