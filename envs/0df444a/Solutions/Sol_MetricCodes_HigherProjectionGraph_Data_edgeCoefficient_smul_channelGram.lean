-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.edgeCoefficient_smul_channelGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/676712e2-2d2a-4de2-9800-a56b05f0fa97

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
theorem _root_.solution [Nonempty I]
    (target source : I) :
    (A.edgeCoefficient target source ^ 2) •
      (if 0 < A.probability target source then A.block source else 0) =
        (A.edgeCoefficient target source ^ 2) • A.block source := by
  split_ifs with hp
  · rfl
  · have hzero : A.probability target source = 0 :=
      le_antisymm (le_of_not_gt hp)
        (A.probability_nonneg target source)
    simp [edgeCoefficient, hzero]
end MetricCodes.HigherProjectionGraph.Data
