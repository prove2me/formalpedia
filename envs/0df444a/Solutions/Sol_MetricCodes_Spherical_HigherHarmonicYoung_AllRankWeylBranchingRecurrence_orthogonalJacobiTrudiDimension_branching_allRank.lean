-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence.orthogonalJacobiTrudiDimension_branching_allRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/f879b898-0be9-4502-8437-4eff1b9b5112

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankWeylBranchingDeterminantSum_orthogonalJacobiTrudiDimension_eq_branchSum_of_rowSum
import Theorems.Thm_MetricCodes_Spherical_HigherYoungOrthogonalBranchCompleteCoefficient_orthogonalCompleteSymmetricCoefficient_dimension_sum_subtype
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankWeylBranchingRecurrence_orthogonalBranchRows_eq_adjacentRowDifference_of_interval

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
    {r n : ℕ} (hn : 2 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    orthogonalJacobiTrudiDimension n lam =
      ∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu) := by
  have hrows := orthogonalBranchRows_eq_adjacentRowDifference_of_interval
    lam hdom (fun L U hLU shift =>
      orthogonalCompleteSymmetricCoefficient_dimension_sum_subtype
        hn hLU shift)
  apply orthogonalJacobiTrudiDimension_eq_branchSum_of_rowSum lam
  intro i j
  exact congrFun (congrFun hrows i) j
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
