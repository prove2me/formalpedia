-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient.orthogonalCompleteSymmetricCoefficient_dimension_sum_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/455b5304-e1f6-41c8-b7c1-13d5493b4a63

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungOrthogonalBranchCompleteCoefficient_orthogonalCompleteSymmetricCoefficient_dimension_sum_range_add

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
    {n : ℕ} (hn : 2 ≤ n) {L U : ℕ} (hLU : L ≤ U) (shift : ℤ) :
    (∑ k ∈ Finset.Icc L U,
      orthogonalCompleteSymmetricCoefficient (n - 1) ((k : ℤ) + shift)) =
      orthogonalCompleteSymmetricCoefficient n ((U : ℤ) + shift) -
        orthogonalCompleteSymmetricCoefficient n (((L : ℤ) - 1) + shift) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sub _ (show L ≤ U + 1 by omega)]
  rw [orthogonalCompleteSymmetricCoefficient_dimension_sum_range_add hn shift
    (U + 1),
    orthogonalCompleteSymmetricCoefficient_dimension_sum_range_add hn shift L]
  push_cast
  have hupper : (U : ℤ) + 1 + shift - 1 = (U : ℤ) + shift := by omega
  have hlower : (L : ℤ) + shift - 1 = ((L : ℤ) - 1) + shift := by omega
  rw [hupper, hlower]
  ring
end MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
