-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.matrixFeature_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/5b3fe13d-569e-4125-9487-dc01c3c67aed

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
theorem _root_.solution (M N : Matrix (Fin Q) (Fin D) ℝ) :
    ⟪matrixFeature M, matrixFeature N⟫_ℝ =
      Matrix.trace (Mᵀ * N) := by
  rw [PiLp.inner_apply]
  simp only [matrixFeature, WithLp.ofLp_toLp, Real.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
end MetricCodes.HigherProjectionGraph.Data
