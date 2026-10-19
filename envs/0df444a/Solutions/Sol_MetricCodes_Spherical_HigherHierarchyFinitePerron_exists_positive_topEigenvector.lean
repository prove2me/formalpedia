-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.exists_positive_topEigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/4773fd93-d252-44b9-b5e3-321809a5c099

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_exists_nonnegative_topEigenvector
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_eigenvector_pos_of_irreducible

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
    (hsymm : Aᵀ = A) (hirreducible : A.IsIrreducible) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 < x i := by
  obtain ⟨x, hx, heig, hnonneg⟩ :=
    exists_nonnegative_topEigenvector A hsymm hirreducible.nonneg
  exact ⟨x, hx, heig,
    eigenvector_pos_of_irreducible A hirreducible x hx hnonneg
      (topEigenvalue A) heig⟩
end MetricCodes.Spherical.HigherHierarchyFinitePerron
