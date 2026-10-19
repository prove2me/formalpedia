-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.exists_topEigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/cd0e8f3e-6041-4270-8663-e94fa4cb6a3a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_operator_isSymmetric

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
    (hA : Aᵀ = A) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x := by
  have h := (operator_isSymmetric A hA).hasEigenvalue_iSup_of_finiteDimensional
  have hvalue :
      Module.End.HasEigenvalue (operator A) (topEigenvalue A) := by
    simpa [topEigenvalue, rayleigh, continuousOperator,
      ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using h
  obtain ⟨x, hx⟩ := hvalue.exists_hasEigenvector
  exact ⟨x, hx.2, hx.apply_eq_smul⟩
end MetricCodes.Spherical.HigherHierarchyFinitePerron
