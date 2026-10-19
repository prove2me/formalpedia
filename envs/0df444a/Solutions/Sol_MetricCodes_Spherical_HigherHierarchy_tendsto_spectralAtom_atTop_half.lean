-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_spectralAtom_atTop_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/84ad7ef2-afcf-45ce-85f1-a77f453e6e2a

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
theorem _root_.solution :
    Tendsto spectralAtom atTop (nhds ((1 : ℝ) / 2)) := by
  have hinv : Tendsto (fun u : ℝ => u⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hnormal :
      Tendsto (fun u : ℝ =>
        Real.sqrt (1 + u⁻¹) / (u⁻¹ + 2)) atTop (nhds ((1 : ℝ) / 2)) := by
    convert ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).sqrt.div
      (hinv.add_const 2) (by norm_num : (0 : ℝ) + 2 ≠ 0) using 1 <;>
      norm_num <;> rfl
  apply hnormal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  unfold spectralAtom quadraticCoordinate
  have hfactor : u * (1 + u) = u ^ 2 * (1 + u⁻¹) := by
    field_simp [hu.ne']
    ring
  rw [hfactor, Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq_eq_abs,
    abs_of_pos hu]
  field_simp [hu.ne']
end MetricCodes.Spherical.HigherHierarchy
