-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure.gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/29eb9f73-771c-4a0c-b09b-e673059b82b8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseEmbedding_orthogonal
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_orthogonal
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_inner_transverse_eq_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisTransverse_iSup_range_eq_top
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalSelectedTwoBlockClosure_linearIsometry_range_starProjection
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalSelectedTwoBlockClosure_mem_submodule_of_complete_orthogonal_two_family_projections

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
set_option maxHeartbeats 4000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam)
    (S : Submodule ℝ
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (x : SpherePacking.Euclidean (n + 1) ⊗[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (haxis : ∀ mu : FullBranchWeight lam,
      gtFullAxisEmbedding lam hn mu
        ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint x) ∈ S)
    (htransverse : ∀ mu : FullBranchWeight lam,
      gtFullTransverseEmbedding lam hn mu
        ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint x) ∈ S) :
    x ∈ S := by
  apply mem_submodule_of_complete_orthogonal_two_family_projections
    (fun mu : FullBranchWeight lam =>
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap)
    (fun mu : FullBranchWeight lam =>
      LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap)
    (S := S) (x := x)
  · intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact gtFullAxisEmbedding_orthogonal lam hn i j hij p q
  · intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact gtFullTransverseEmbedding_orthogonal lam hn i j hij p q
  · intro i j
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact gtFullAxisEmbedding_inner_transverse_eq_zero lam hn i j p q
  · exact gtFullAxisTransverse_iSup_range_eq_top lam hn hdom
  · intro i
    rw [linearIsometry_range_starProjection]
    exact haxis i
  · intro i
    rw [linearIsometry_range_starProjection]
    exact htransverse i
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure
