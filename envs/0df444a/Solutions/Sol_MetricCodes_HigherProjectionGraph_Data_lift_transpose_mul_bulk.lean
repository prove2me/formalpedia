-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.lift_transpose_mul_bulk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/fc71881e-a215-4edc-be1e-a6fc7748b965

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_projection_axis_transpose_assembled

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
    (A.lift x)ᵀ * A.bulk y =
      Real.sqrt A.eigenvalue •
        (A.combinedProjection x * A.combinedProjection y) := by
  unfold lift bulk
  calc
    (A.axis x * A.combinedProjection x)ᵀ *
        (A.assembledChannel * A.combinedProjection y) =
      (A.combinedProjection x * (A.axis x)ᵀ *
        A.assembledChannel) * A.combinedProjection y := by
          simp [Matrix.transpose_mul,
            A.combinedProjection_symmetric x, Matrix.mul_assoc]
    _ = _ := by
      rw [A.projection_axis_transpose_assembled x,
        Matrix.smul_mul]
end MetricCodes.HigherProjectionGraph.Data
