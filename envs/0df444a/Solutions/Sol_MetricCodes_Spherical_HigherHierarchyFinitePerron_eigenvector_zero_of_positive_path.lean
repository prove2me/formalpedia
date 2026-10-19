-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.eigenvector_zero_of_positive_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/bfd3ea19-88f1-489c-a97f-02832c385695

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_eigenvector_zero_of_positive_edge

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
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Metric
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherHierarchyFinitePerron
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
namespace MetricCodes.Spherical.HigherHierarchyFinitePerron
theorem _root_.solution (A : Matrix I I ℝ)
    (hnonneg : ∀ i j : I, 0 ≤ A i j)
    (x : Space I) (hx : ∀ i : I, 0 ≤ x i)
    (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x)
    {i j : I} (p : @Quiver.Path I (Matrix.toQuiver A) i j)
    (hzero : x i = 0) : x j = 0 := by
  induction p with
  | nil => exact hzero
  | @cons j k p e ih =>
      exact eigenvector_zero_of_positive_edge A hnonneg x hx
        eigenvalue heig ih e.down
end MetricCodes.Spherical.HigherHierarchyFinitePerron
