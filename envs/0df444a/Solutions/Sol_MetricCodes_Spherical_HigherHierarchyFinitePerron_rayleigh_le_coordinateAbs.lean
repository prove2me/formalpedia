-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.rayleigh_le_coordinateAbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/4020cb99-4822-48d1-a055-d66a211897c0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_coordinateAbs_norm
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_inner_le_inner_coordinateAbs

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
    (hA : ∀ i j : I, 0 ≤ A i j) (x : Space I) :
    rayleigh A x ≤ rayleigh A (coordinateAbs x) := by
  change
    @inner ℝ (Space I) _ (operator A x) x / ‖x‖ ^ 2 ≤
      @inner ℝ (Space I) _ (operator A (coordinateAbs x))
        (coordinateAbs x) / ‖coordinateAbs x‖ ^ 2
  rw [coordinateAbs_norm]
  gcongr
  exact inner_le_inner_coordinateAbs A hA x
end MetricCodes.Spherical.HigherHierarchyFinitePerron
