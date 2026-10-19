-- Prove2me | solution 1 for MetricCodes.HigherProjectionGraph.Data.code_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/ac044b66-373f-45bd-ab7c-2f9934724c54

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_projection_certificate
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_remainderFeature_inner
import Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_ambientDimension_eq_sum

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
    (C : Finset X) {s : ℝ}
    (hd : 0 < d)
    (hs : s < 1)
    (hgap : s < A.eigenvalue)
    (hdiag : ∀ x ∈ C, A.correlation x x = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C,
      x ≠ y → A.correlation x y ≤ s) :
    (C.card : ℝ) ≤
      ((1 - s) / (A.eigenvalue - s)) *
        ((∑ i, (A.dimension i : ℝ)) / (d : ℝ)) := by
  have h := MetricCodes.projection_certificate
    A.projectionFamily C A.correlation A.remainderFeature
    hd hs hgap hdiag hsep
    (fun x _ y _ => A.remainderFeature_inner x y)
  rw [A.ambientDimension_eq_sum] at h
  exact h
end MetricCodes.HigherProjectionGraph.Data
