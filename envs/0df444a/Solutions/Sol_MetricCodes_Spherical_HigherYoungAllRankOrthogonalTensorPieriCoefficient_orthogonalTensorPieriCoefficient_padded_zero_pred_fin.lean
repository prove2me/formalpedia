-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient.orthogonalTensorPieriCoefficient_padded_zero_pred_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/7058be8f-90b9-47ea-9561-762e24859e4a

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
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
theorem _root_.solution
    (n r : ℕ) (j : Fin (r + 1)) :
    orthogonalTensorPieriCoefficient n (-(r : ℤ) - 1) (j.val : ℤ) = 0 := by
  unfold orthogonalTensorPieriCoefficient
  have hj := j.isLt
  have hfirst : -(r : ℤ) - 1 + (j.val : ℤ) < 0 := by omega
  have hsecond : -(r : ℤ) - 1 - (j.val : ℤ) - 2 < 0 := by omega
  rw [orthogonalCompleteSymmetricCoefficient_of_neg n hfirst,
    orthogonalCompleteSymmetricCoefficient_of_neg n hsecond]
  rfl
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
