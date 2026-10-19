-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence.weylBranchingRecurrence_of_jacobiTrudi_branching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/a9945434-acb0-43ed-8716-f4a9d29a9f74

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
theorem _root_.solution
    {r n : ℕ} (hn : 2 * r + 5 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hbranch : orthogonalJacobiTrudiDimension n lam =
      ∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu)) :
    WeylBranchingRecurrence n lam := by
  unfold WeylBranchingRecurrence
  calc
    Weyl.dimension n lam =
        (orthogonalJacobiTrudiDimension n lam : ℝ) :=
      (orthogonalJacobiTrudiDimension_eq_weyl (by omega) lam).symm
    _ = (∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu) : ℤ) := by
      exact_mod_cast hbranch
    _ = ∑ mu : FullBranchWeight lam,
        (orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu) : ℝ) := by
      rw [Int.cast_sum]
    _ = ∑ mu : FullBranchWeight lam,
        Weyl.dimension (n - 1) (fullBranchSignature mu) := by
      apply Finset.sum_congr rfl
      intro mu _
      exact orthogonalJacobiTrudiDimension_eq_weyl (by omega)
        (fullBranchSignature mu)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
