-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient.orthogonalTensorPieriCoefficient_eq_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/53e33430-e83b-4df0-8bc5-833db2eac00c

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
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) :
    orthogonalJacobiTrudiMatrix n lam i j =
      orthogonalTensorPieriCoefficient n
        ((lam i : ℤ) - (i.val : ℤ)) (j.val : ℤ) := by
  simp [orthogonalJacobiTrudiMatrix, orthogonalTensorPieriCoefficient]
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
