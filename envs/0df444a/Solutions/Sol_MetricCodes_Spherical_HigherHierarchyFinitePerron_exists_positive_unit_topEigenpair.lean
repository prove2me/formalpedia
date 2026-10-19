-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.exists_positive_unit_topEigenpair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/b5b7c0ae-447c-4a0f-bc5a-078a180960af

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_exists_positive_unit_topEigenvector
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_unit_coordinate_sq_sum

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
    ∃ x : I → ℝ,
      (∀ i : I, 0 < x i) ∧
      (∑ i : I, x i ^ 2) = 1 ∧
      (∀ i : I, ∑ j : I, A i j * x j = topEigenvalue A * x i) := by
  obtain ⟨x, hunit, heig, hpos⟩ :=
    exists_positive_unit_topEigenvector A hsymm hirreducible
  refine ⟨fun i => x i, hpos, unit_coordinate_sq_sum hunit, ?_⟩
  intro i
  have h := congrArg (fun z : Space I => z i) heig
  exact h
end MetricCodes.Spherical.HigherHierarchyFinitePerron
