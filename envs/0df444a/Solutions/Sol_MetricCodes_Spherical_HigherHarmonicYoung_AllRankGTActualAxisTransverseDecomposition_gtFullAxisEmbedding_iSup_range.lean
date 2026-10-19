-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition.gtFullAxisEmbedding_iSup_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/d74108fe-915d-47cc-b634-7232adaf62fc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranch_iSup_range_eq_top_unconditional

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap) =
        LinearMap.range
          (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap := by
  calc
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap) =
        ⨆ mu : FullBranchWeight lam,
          (LinearMap.range
            (canonicalFullBranchFibre lam hn mu).toLinearMap).map
              (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap := by
          congr 1
          funext mu
          change
            LinearMap.range
                ((gtFullAxisAmbientInclusion (n := n) lam).toLinearMap.comp
                  (canonicalFullBranchFibre lam hn mu).toLinearMap) = _
          rw [LinearMap.range_comp]
    _ = (⨆ mu : FullBranchWeight lam,
          LinearMap.range (canonicalFullBranchFibre lam hn mu).toLinearMap).map
            (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap :=
          (Submodule.map_iSup _ _).symm
    _ = (⊤ : Submodule ℝ
          (HarmonicYoungSpace (n := n + 1) lam)).map
            (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap := by
          rw [canonicalFullBranch_iSup_range_eq_top_unconditional
            lam hn hdom]
    _ = LinearMap.range
          (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap :=
          Submodule.map_top _
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
