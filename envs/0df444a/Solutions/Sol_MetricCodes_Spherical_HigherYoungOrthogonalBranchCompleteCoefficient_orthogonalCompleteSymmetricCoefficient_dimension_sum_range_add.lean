-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient.orthogonalCompleteSymmetricCoefficient_dimension_sum_range_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/4050ef26-f588-49d6-817e-ae52b7b61b0e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungOrthogonalBranchCompleteCoefficient_orthogonalCompleteSymmetricCoefficient_dimension_sum_range

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
    {n : ℕ} (hn : 2 ≤ n) (shift : ℤ) (q : ℕ) :
    (∑ j ∈ Finset.range q,
      orthogonalCompleteSymmetricCoefficient (n - 1) ((j : ℤ) + shift)) =
      orthogonalCompleteSymmetricCoefficient n ((q : ℤ) + shift - 1) -
        orthogonalCompleteSymmetricCoefficient n (shift - 1) := by
  simpa [add_comm] using
    orthogonalCompleteSymmetricCoefficient_dimension_sum_range hn shift q
end MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
