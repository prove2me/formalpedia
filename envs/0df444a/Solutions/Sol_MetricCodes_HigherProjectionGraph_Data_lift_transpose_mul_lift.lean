-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.lift_transpose_mul_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/7d1e2d60-e1f6-4347-a51d-7a96198ecc44

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
open MetricCodes
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open MetricCodes.HigherProjectionGraph
variable {I X : Type*} [Fintype I] [DecidableEq I]
open MetricCodes.HigherProjectionGraph.Data
variable {D d Q : ℕ} (A : Data I X D d Q)
namespace MetricCodes.HigherProjectionGraph.Data
theorem _root_.solution [Nonempty I] (x y : X) :
    (A.lift x)ᵀ * A.lift y =
      A.correlation x y •
        (A.combinedProjection x * A.combinedProjection y) := by
  unfold lift
  rw [Matrix.transpose_mul, A.combinedProjection_symmetric x,
    Matrix.mul_assoc, ← Matrix.mul_assoc (A.axis x)ᵀ,
    A.axis_inner x y]
  simp
end MetricCodes.HigherProjectionGraph.Data
