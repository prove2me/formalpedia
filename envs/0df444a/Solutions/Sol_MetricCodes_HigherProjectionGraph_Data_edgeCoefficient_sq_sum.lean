-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.edgeCoefficient_sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/4ff44e96-9f1b-4e5e-9c1d-0cdf1a1eccb0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_amplitude_pos
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_amplitude_eigenvector_equation
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_edgeCoefficient_sq

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
theorem _root_.solution [Nonempty I] (source : I) :
    (∑ target, A.edgeCoefficient target source ^ 2) = 1 := by
  simp_rw [A.edgeCoefficient_sq]
  rw [← Finset.sum_div, A.amplitude_eigenvector_equation]
  exact div_self
    (mul_ne_zero A.eigenvalue_pos.ne'
      (pow_ne_zero _ (A.amplitude_pos source).ne'))
end MetricCodes.HigherProjectionGraph.Data
