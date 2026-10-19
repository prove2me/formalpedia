-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum.sum_orthogonalJacobiTrudiDimension_eq_det_branchRowSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/43c3fb7e-bbbd-424a-bf29-96ca34367e1f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankWeylBranchingDeterminantSum_sum_det_eq_det_rowSum

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    (∑ mu : FullBranchWeight lam,
      orthogonalJacobiTrudiDimension n (fullBranchSignature mu)) =
      Matrix.det (fun i j =>
        ∑ x : {a : Fin (lam i + 1) // branchLower lam i ≤ a.val},
          branchJacobiTrudiRow n lam i x j) := by
  classical
  let row : ∀ i : Fin (r + 1),
      {a : Fin (lam i + 1) // branchLower lam i ≤ a.val} →
        Fin (r + 1) → ℤ :=
    branchJacobiTrudiRow n lam
  calc
    (∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension n (fullBranchSignature mu)) =
      ∑ x : (∀ i : Fin (r + 1),
          {a : Fin (lam i + 1) // branchLower lam i ≤ a.val}),
        Matrix.det (fun i j => row i (x i) j) := by
      rw [← (fullBranchWeightProductEquiv lam).sum_comp]
      apply Finset.sum_congr rfl
      intro mu _
      unfold orthogonalJacobiTrudiDimension orthogonalJacobiTrudiMatrix
      congr 1
    _ = Matrix.det (fun i j => ∑ x, row i x j) :=
      sum_det_eq_det_rowSum row
    _ = _ := rfl
end MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
