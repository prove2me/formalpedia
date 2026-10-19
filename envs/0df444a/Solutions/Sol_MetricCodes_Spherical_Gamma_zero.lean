-- Prove2me | solution 1 for MetricCodes.Spherical.Gamma_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/29ed5899-638e-4551-9554-2c27259aeeeb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Gamma_eq_sub

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    MetricCodes.Gamma a 0 =
      Real.sqrt (a * (1 + a)) / (1 + 2 * a) := by
  have hrad : 0 < a * (1 + a) := by positivity
  have hroot : Real.sqrt (a * (1 + a)) ≠ 0 :=
    (Real.sqrt_pos.2 hrad).ne'
  have hlin : 1 + 2 * a ≠ 0 := by positivity
  have hsquare := Real.sq_sqrt hrad.le
  rw [MetricCodes.Gamma_eq_sub]
  simp only [zero_mul, add_zero, sub_zero]
  field_simp [hroot, hlin]
  nlinarith
end MetricCodes.Spherical
