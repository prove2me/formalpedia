-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransversePhysicalDiagonalColumn.normalizedWallSector_selectedFullTensor_adjoint_eigen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/9f9885a7-e5ba-495f-9797-bbefa83413e0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTFullTransverseSameSignatureRow_adjoint_eigen_of_range_le
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallFullTransverseFactorization_gtTransverseWallTensorEmbedding_range_eq_fullTransverse
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransversePhysicalDiagonalColumn_normalizedWallSector_shortTensor_adjoint_eigen
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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransversePhysicalDiagonalColumn
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransversePhysicalDiagonalColumn
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    let J := gtFullTransverseEmbedding lam hn
      (gtWallFullBranch lam mu h hlast)
    let B := normalizedGTTransverseWallSector lam mu h hn hlast
    let d := -(wallShift (n + 1) (r + 1))
    J.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • J.toLinearMap.adjoint (B p) := by
  dsimp
  apply adjoint_eigen_of_range_le
    (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap
    (gtFullTransverseEmbedding lam hn
      (gtWallFullBranch lam mu h hlast)).toLinearMap
    (le_of_eq
      (gtTransverseWallTensorEmbedding_range_eq_fullTransverse
        lam mu h hn hlast).symm)
    (gtRelativeCasimir (n := n + 1) lam)
    (normalizedGTTransverseWallSector lam mu h hn hlast p)
    (-(wallShift (n + 1) (r + 1)))
  exact normalizedWallSector_shortTensor_adjoint_eigen
    lam mu h hn hlast p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransversePhysicalDiagonalColumn
