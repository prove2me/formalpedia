-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.bulk_transpose_mul_bulk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/dd18f8de-3c35-4015-b4ab-38aa0e9d9908

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_assembledChannel_isometry

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
    (A.bulk x)ᵀ * A.bulk y =
      A.combinedProjection x * A.combinedProjection y := by
  unfold bulk
  rw [Matrix.transpose_mul, A.combinedProjection_symmetric x,
    Matrix.mul_assoc,
    ← Matrix.mul_assoc (A.assembledChannel)ᵀ,
    A.assembledChannel_isometry]
  simp
end MetricCodes.HigherProjectionGraph.Data
