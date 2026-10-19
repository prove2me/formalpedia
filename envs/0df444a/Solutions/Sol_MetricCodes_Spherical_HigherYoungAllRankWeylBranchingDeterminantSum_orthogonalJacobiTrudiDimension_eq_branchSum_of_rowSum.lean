-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum.orthogonalJacobiTrudiDimension_eq_branchSum_of_rowSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/a4ea95fe-3dae-4856-a518-c0adbc845e33

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankWeylBranchingRowDifference_det_adjacentRowDifference
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankWeylBranchingDeterminantSum_sum_orthogonalJacobiTrudiDimension_eq_det_branchRowSum

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
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
namespace MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hrow : ∀ (i j : Fin (r + 1)),
      (∑ x : {a : Fin (lam i + 1) // branchLower lam i ≤ a.val},
        branchJacobiTrudiRow (n - 1) lam i x j) =
        adjacentRowDifference (orthogonalJacobiTrudiMatrix n lam) i j) :
    orthogonalJacobiTrudiDimension n lam =
      ∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu) := by
  calc
    orthogonalJacobiTrudiDimension n lam =
        Matrix.det (adjacentRowDifference
          (orthogonalJacobiTrudiMatrix n lam)) := by
      exact (det_adjacentRowDifference
        (orthogonalJacobiTrudiMatrix n lam)).symm
    _ = Matrix.det (fun i j =>
        ∑ x : {a : Fin (lam i + 1) // branchLower lam i ≤ a.val},
          branchJacobiTrudiRow (n - 1) lam i x j) := by
      congr 1
      funext i j
      exact (hrow i j).symm
    _ = _ :=
      (sum_orthogonalJacobiTrudiDimension_eq_det_branchRowSum
        (n := n - 1) lam).symm
end MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
