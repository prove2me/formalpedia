-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.remainderFeature_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/4b5c9e1f-f04c-4838-a1b4-dc5986de1d5e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_remainder_transpose_mul
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_matrixFeature_inner

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
    ⟪A.remainderFeature x, A.remainderFeature y⟫_ℝ =
      (A.correlation x y - A.eigenvalue) *
        (A.projectionFamily).overlap x y := by
  unfold remainderFeature
  rw [matrixFeature_inner, A.remainder_transpose_mul]
  simp [MetricCodes.ProjectionFamily.overlap,
    projectionFamily, Matrix.trace_smul]
end MetricCodes.HigherProjectionGraph.Data
