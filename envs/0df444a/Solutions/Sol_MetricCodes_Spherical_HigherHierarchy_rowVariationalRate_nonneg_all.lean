-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.rowVariationalRate_nonneg_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/7d981082-b0b7-40f9-a1c3-4c45b2a49811

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_sub_nonneg

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution (s : ℝ) :
    0 ≤ MetricCodes.Spherical.variationalRate s := by
  by_cases hnonempty : (MetricCodes.Spherical.rateSet s).Nonempty
  · unfold MetricCodes.Spherical.variationalRate
    apply le_csInf hnonempty
    rintro _ ⟨a, b, hfeasible, rfl⟩
    exact MetricCodes.Spherical.sphericalEntropy_sub_nonneg
      hfeasible.1.le hfeasible.2.1.le
  · have hempty : MetricCodes.Spherical.rateSet s = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp [MetricCodes.Spherical.variationalRate, hempty]
end MetricCodes.Spherical.HigherHierarchy
