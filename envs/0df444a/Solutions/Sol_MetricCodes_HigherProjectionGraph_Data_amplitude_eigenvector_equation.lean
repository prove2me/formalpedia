-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.amplitude_eigenvector_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/4df74008-41e6-4234-b67e-611c9b2a33ab

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_weighted_eigenvector_equation

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
    (∑ target,
      A.probability target source * A.amplitude target ^ 2) =
      A.eigenvalue * A.amplitude source ^ 2 := by
  simp_rw [A.amplitude_sq]
  calc
    (∑ target,
      A.probability target source *
        (A.weight target / A.normalization)) =
        (∑ target, A.probability target source * A.weight target) /
          A.normalization := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro target _
            ring
    _ = A.eigenvalue * (A.weight source / A.normalization) := by
          rw [A.weighted_eigenvector_equation source]
          ring
end MetricCodes.HigherProjectionGraph.Data
