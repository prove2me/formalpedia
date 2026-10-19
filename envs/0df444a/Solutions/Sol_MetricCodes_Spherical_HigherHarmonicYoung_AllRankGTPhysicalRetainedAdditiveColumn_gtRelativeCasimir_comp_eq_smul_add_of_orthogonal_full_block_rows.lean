-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalRetainedAdditiveColumn.gtRelativeCasimir_comp_eq_smul_add_of_orthogonal_full_block_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/f25e591b-cd60-46fc-8626-81fd8424b8ba

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalRetainedAdditiveColumn_gtRelativeCasimir_comp_eq_smul_add_of_full_axis_transverse_rows

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam)
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (B : E →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (A : F →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (haxisOrth : ∀ mu : FullBranchWeight lam,
      (gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp B = 0)
    (htransverseOrth : ∀ mu : FullBranchWeight lam,
      (gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp A = 0)
    (haxis : ∀ mu : FullBranchWeight lam,
      (gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp A).comp K)
    (htransverse : ∀ mu : FullBranchWeight lam,
      (gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        d • ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp B)) :
    (gtRelativeCasimir (n := n + 1) lam).comp B =
      d • B + A.comp K := by
  apply gtRelativeCasimir_comp_eq_smul_add_of_full_axis_transverse_rows
    lam hn hdom B A K d
  · intro mu
    rw [haxisOrth mu, smul_zero, zero_add, haxis mu]
  · intro mu
    rw [htransverseOrth mu, LinearMap.zero_comp, add_zero,
      htransverse mu]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalRetainedAdditiveColumn
