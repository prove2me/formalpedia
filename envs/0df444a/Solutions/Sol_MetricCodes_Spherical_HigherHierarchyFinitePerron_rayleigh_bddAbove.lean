-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.rayleigh_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/d7c701c4-3a47-4d52-b21f-06e370184f1c

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
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Metric
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherHierarchyFinitePerron
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
namespace MetricCodes.Spherical.HigherHierarchyFinitePerron
theorem _root_.solution (A : Matrix I I ℝ) :
    BddAbove
      (Set.range (fun x : {x : Space I // x ≠ 0} => rayleigh A x)) := by
  refine ⟨‖continuousOperator A‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (le_abs_self _).trans
    ((continuousOperator A).rayleighQuotient_le_norm x)
end MetricCodes.Spherical.HigherHierarchyFinitePerron
