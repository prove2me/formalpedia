-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient.orthogonalTensorPieriCoefficient_lower_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/1c53d74c-f981-438c-b62c-800861786169

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriCoefficient_orthogonalTensorPieriCoefficient_eq_matrix

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
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
theorem _root_.solution
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hi : 0 < lam i) :
    orthogonalJacobiTrudiMatrix n
        (Function.update lam i (lam i - 1)) i j =
      orthogonalTensorPieriCoefficient n
        (((lam i : ℤ) - (i.val : ℤ)) - 1) (j.val : ℤ) := by
  rw [orthogonalTensorPieriCoefficient_eq_matrix]
  simp only [Function.update_self]
  rw [Nat.cast_sub (show 1 ≤ lam i by omega)]
  norm_num
  congr 1
  ring
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
