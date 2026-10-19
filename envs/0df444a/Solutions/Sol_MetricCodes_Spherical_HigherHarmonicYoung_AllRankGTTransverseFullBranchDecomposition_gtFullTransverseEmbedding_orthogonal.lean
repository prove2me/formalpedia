-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition.gtFullTransverseEmbedding_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/a0714042-c7ee-454f-a95e-55169d529afb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_orthogonal
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseEmbedding_eq_comp

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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
theorem _root_.solution {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu nu : FullBranchWeight lam) (hne : mu ≠ nu)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (y : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪gtFullTransverseEmbedding lam hn mu x,
      gtFullTransverseEmbedding lam hn nu y⟫_ℝ = 0 := by
  have hmu := LinearMap.congr_fun
    (gtFullTransverseEmbedding_eq_comp lam hn mu) x
  have hnu := LinearMap.congr_fun
    (gtFullTransverseEmbedding_eq_comp lam hn nu) y
  change
    ⟪(gtFullTransverseEmbedding lam hn mu).toLinearMap x,
      (gtFullTransverseEmbedding lam hn nu).toLinearMap y⟫_ℝ = 0
  rw [hmu, hnu]
  calc
    _ = ⟪gtFullTransverseInternalEmbedding lam hn mu x,
          gtFullTransverseInternalEmbedding lam hn nu y⟫_ℝ :=
      (gtFullTransverseAmbientInclusion (n := n) lam).inner_map_map _ _
    _ = 0 :=
      gtFullTransverseInternalEmbedding_orthogonal lam hn mu nu hne x y
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
