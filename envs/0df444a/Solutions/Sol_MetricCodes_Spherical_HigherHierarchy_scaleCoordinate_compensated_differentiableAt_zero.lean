-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.scaleCoordinate_compensated_differentiableAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/cd9deacb-2c95-4dbe-8d8a-9b944dd754ad

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    DifferentiableAt ℝ
      (fun ε => scaleCoordinate (compensatedScalingFactor a b ε) u) 0 := by
  have hquad : 0 ≤ quadraticCoordinate u := by
    unfold quadraticCoordinate
    positivity
  have hinner : DifferentiableAt ℝ
      (fun ε => 1 + 4 * compensatedScalingFactor a b ε * quadraticCoordinate u)
      0 := by
    fun_prop
  have hrad :
      1 + 4 * compensatedScalingFactor a b 0 * quadraticCoordinate u ≠ 0 := by
    rw [compensatedScalingFactor_zero]
    positivity
  unfold scaleCoordinate
  exact ((hinner.sqrt hrad).sub_const 1).div_const 2
end MetricCodes.Spherical.HigherHierarchy
