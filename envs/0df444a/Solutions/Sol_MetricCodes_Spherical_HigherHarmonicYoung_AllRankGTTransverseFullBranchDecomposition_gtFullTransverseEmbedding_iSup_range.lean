-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition.gtFullTransverseEmbedding_iSup_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:48.515695+00:00
-- url     : https://prove2.me/submissions/82fd9afe-ae94-4548-ad07-9c5648f48925

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_iSup_range_eq_top
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
    (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap) =
      LinearMap.range
        (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap := by
  calc
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap) =
        ⨆ mu : FullBranchWeight lam,
          (LinearMap.range
            (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap).map
              (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap := by
          congr 1
          funext mu
          rw [gtFullTransverseEmbedding_eq_comp, LinearMap.range_comp]
    _ = (⨆ mu : FullBranchWeight lam,
          LinearMap.range
            (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap).map
              (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap :=
          (Submodule.map_iSup _ _).symm
    _ = (⊤ : Submodule ℝ
          (SpherePacking.Euclidean n ⊗[ℝ]
            HarmonicYoungSpace (n := n + 1) lam)).map
              (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap := by
          rw [gtFullTransverseInternalEmbedding_iSup_range_eq_top
            lam hn hdom]
    _ = LinearMap.range
          (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap :=
          Submodule.map_top _
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
