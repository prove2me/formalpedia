-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_retainedQuadraticResidueFactor_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/09db6ad5-13db-495a-bd04-3ae9dcc214b5

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    (z c : ℝ) :
    Tendsto (fun u : ℝ =>
      (quadraticCoordinate z - c ^ 2 * quadraticCoordinate u) /
        (quadraticCoordinate z - quadraticCoordinate u))
      atTop (nhds (c ^ 2)) := by
  have hu : Tendsto (fun u : ℝ => u⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hq : Tendsto (fun u : ℝ => (quadraticCoordinate u)⁻¹)
      atTop (nhds 0) := by
    have hnorm : Tendsto (fun u : ℝ => u⁻¹ * (1 + u)⁻¹)
        atTop (nhds 0) := by
      have hshift : Tendsto (fun u : ℝ => (1 + u)⁻¹)
          atTop (nhds 0) := by
        exact tendsto_inv_atTop_zero.comp
          ((tendsto_const_nhds (x := (1 : ℝ))).add_atTop tendsto_id)
      simpa using hu.mul hshift
    simpa [quadraticCoordinate, mul_comm] using hnorm
  have hnormal :
      Tendsto (fun u : ℝ =>
        (quadraticCoordinate z * (quadraticCoordinate u)⁻¹ - c ^ 2) /
          (quadraticCoordinate z * (quadraticCoordinate u)⁻¹ - 1))
        atTop (nhds (c ^ 2)) := by
    convert ((hq.const_mul (quadraticCoordinate z)).sub_const (c ^ 2)).div
      ((hq.const_mul (quadraticCoordinate z)).sub_const 1)
      (by norm_num : (quadraticCoordinate z * 0 - 1 : ℝ) ≠ 0) using 1 <;>
      norm_num <;> rfl
  apply hnormal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hquad : quadraticCoordinate u ≠ 0 := by
    unfold quadraticCoordinate
    positivity
  field_simp [hquad]
end MetricCodes.Spherical.HigherHierarchy
