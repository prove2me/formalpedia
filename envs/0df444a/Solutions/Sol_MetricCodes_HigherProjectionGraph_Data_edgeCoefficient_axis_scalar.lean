-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.edgeCoefficient_axis_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/a92d74c2-c9e0-43e3-af81-7b4e2b72997d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_amplitude_pos

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
theorem _root_.solution [Nonempty I]
    (target source : I) :
    A.edgeCoefficient target source * A.amplitude target *
        Real.sqrt (A.probability target source) =
      A.probability target source * A.amplitude target ^ 2 /
        (Real.sqrt A.eigenvalue * A.amplitude source) := by
  unfold edgeCoefficient
  have hp := A.probability_nonneg target source
  have he : Real.sqrt A.eigenvalue ≠ 0 :=
    (Real.sqrt_pos.2 A.eigenvalue_pos).ne'
  have ha : A.amplitude source ≠ 0 :=
    (A.amplitude_pos source).ne'
  field_simp
  nlinarith [Real.sq_sqrt hp]
end MetricCodes.HigherProjectionGraph.Data
