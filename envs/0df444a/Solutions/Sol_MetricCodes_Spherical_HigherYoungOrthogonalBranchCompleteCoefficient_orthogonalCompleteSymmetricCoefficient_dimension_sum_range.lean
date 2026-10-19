-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient.orthogonalCompleteSymmetricCoefficient_dimension_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/36210de9-5981-4226-bab8-b0e7e682bbec

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungOrthogonalBranchCompleteCoefficient_orthogonalCompleteSymmetricCoefficient_dimension_sub

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
open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
namespace MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
theorem _root_.solution
    {n : ℕ} (hn : 2 ≤ n) (a : ℤ) (q : ℕ) :
    (∑ j ∈ Finset.range q,
      orthogonalCompleteSymmetricCoefficient (n - 1) (a + (j : ℤ))) =
      orthogonalCompleteSymmetricCoefficient n (a + (q : ℤ) - 1) -
        orthogonalCompleteSymmetricCoefficient n (a - 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := orthogonalCompleteSymmetricCoefficient_dimension_sub
        hn (a + (q : ℤ))
      push_cast
      have hnext : a + ((q : ℤ) + 1) - 1 = a + (q : ℤ) := by omega
      rw [hnext]
      omega
end MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
