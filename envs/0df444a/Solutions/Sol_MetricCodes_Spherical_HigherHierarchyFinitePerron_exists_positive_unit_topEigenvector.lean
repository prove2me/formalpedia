-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.exists_positive_unit_topEigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/ba7e568d-4012-4957-bf2c-edbd975bf24e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_exists_positive_topEigenvector

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
    ∃ x : Space I,
      ‖x‖ = 1 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 < x i := by
  obtain ⟨x, hx, heig, hpos⟩ :=
    exists_positive_topEigenvector A hsymm hirreducible
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    exact inv_mul_cancel₀ hnorm.ne'
  · rw [map_smul, heig]
    exact smul_comm _ _ _
  · intro i
    change 0 < ‖x‖⁻¹ * x i
    exact mul_pos (inv_pos.mpr hnorm) (hpos i)
end MetricCodes.Spherical.HigherHierarchyFinitePerron
