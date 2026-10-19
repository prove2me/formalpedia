-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient.orthogonalTensorPieriCoefficient_row_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/abc8ba09-a336-4c07-b36c-073face7f2bd

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
    (n : ℕ) (z j : ℤ) :
    orthogonalTensorPieriCoefficient n (z + 1) j +
        orthogonalTensorPieriCoefficient n (z - 1) j =
      orthogonalTensorPieriCoefficient n z (j + 1) +
        orthogonalTensorPieriCoefficient n z (j - 1) := by
  unfold orthogonalTensorPieriCoefficient
  have h₁ : z + 1 + j = z + (j + 1) := by ring
  have h₂ : z + 1 - j - 2 = z - (j - 1) - 2 := by ring
  have h₃ : z - 1 + j = z + (j - 1) := by ring
  have h₄ : z - 1 - j - 2 = z - (j + 1) - 2 := by ring
  rw [h₁, h₂, h₃, h₄]
  ring
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
