-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.eigenvector_pos_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/d724322d-d87d-42ec-9aab-777c15b0f869

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_eigenvector_zero_of_positive_path

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
    (hirreducible : A.IsIrreducible)
    (x : Space I) (hxzero : x ≠ 0) (hx : ∀ i : I, 0 ≤ x i)
    (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x) :
    ∀ i : I, 0 < x i := by
  intro i
  by_contra hnot
  have hzero : x i = 0 :=
    le_antisymm (le_of_not_gt hnot) (hx i)
  apply hxzero
  apply PiLp.ext
  intro j
  obtain ⟨p, _⟩ := hirreducible.connected i j
  simpa using eigenvector_zero_of_positive_path A hirreducible.nonneg
    x hx eigenvalue heig p hzero
end MetricCodes.Spherical.HigherHierarchyFinitePerron
