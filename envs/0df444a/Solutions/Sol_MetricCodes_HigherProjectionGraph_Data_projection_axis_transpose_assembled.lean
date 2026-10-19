-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.projection_axis_transpose_assembled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/a627bef0-daf8-4e9b-ba45-e129b68cbe99

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_assembledChannel_axis_projection

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
theorem _root_.solution [Nonempty I] (x : X) :
    A.combinedProjection x * (A.axis x)ᵀ * A.assembledChannel =
      Real.sqrt A.eigenvalue • A.combinedProjection x := by
  have h := congrArg Matrix.transpose
    (A.assembledChannel_axis_projection x)
  simpa [Matrix.transpose_mul,
    A.combinedProjection_symmetric x, Matrix.mul_assoc] using h
end MetricCodes.HigherProjectionGraph.Data
