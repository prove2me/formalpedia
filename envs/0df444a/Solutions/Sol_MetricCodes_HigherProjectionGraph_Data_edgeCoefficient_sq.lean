-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.edgeCoefficient_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/a8fc356b-19dd-4937-953a-404775e56b08

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
theorem _root_.solution [Nonempty I] (target source : I) :
    A.edgeCoefficient target source ^ 2 =
      A.probability target source * A.amplitude target ^ 2 /
        (A.eigenvalue * A.amplitude source ^ 2) := by
  unfold edgeCoefficient
  rw [div_pow, mul_pow, mul_pow,
    Real.sq_sqrt (A.probability_nonneg target source),
    Real.sq_sqrt A.eigenvalue_pos.le]
end MetricCodes.HigherProjectionGraph.Data
