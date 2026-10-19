-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.remainder_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/eec37e98-6c9d-4e07-9afb-4cb59d3c7a43

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_lift_transpose_mul_lift
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_bulk_transpose_mul_bulk
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_lift_transpose_mul_bulk
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_bulk_transpose_mul_lift

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
    (A.remainder x)ᵀ * A.remainder y =
      (A.correlation x y - A.eigenvalue) •
        (A.combinedProjection x * A.combinedProjection y) := by
  unfold remainder
  simp only [Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul]
  rw [A.lift_transpose_mul_lift x y,
    A.lift_transpose_mul_bulk x y,
    A.bulk_transpose_mul_lift x y,
    A.bulk_transpose_mul_bulk x y]
  have hroot := Real.sq_sqrt A.eigenvalue_pos.le
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    A.correlation x y *
          (A.combinedProjection x * A.combinedProjection y) i j -
        Real.sqrt A.eigenvalue *
          (Real.sqrt A.eigenvalue *
            (A.combinedProjection x * A.combinedProjection y) i j) -
        Real.sqrt A.eigenvalue *
          (Real.sqrt A.eigenvalue *
              (A.combinedProjection x * A.combinedProjection y) i j -
            Real.sqrt A.eigenvalue *
              (A.combinedProjection x * A.combinedProjection y) i j) =
        (A.correlation x y - Real.sqrt A.eigenvalue ^ 2) *
          (A.combinedProjection x * A.combinedProjection y) i j := by ring
    _ = _ := by rw [hroot]
end MetricCodes.HigherProjectionGraph.Data
