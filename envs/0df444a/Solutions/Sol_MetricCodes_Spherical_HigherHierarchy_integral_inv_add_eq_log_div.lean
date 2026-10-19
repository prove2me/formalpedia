-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.integral_inv_add_eq_log_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/e26067b4-53d4-4976-a20e-86693e27e39d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {t p q : ℝ} (hp : 0 < t + p) (hq : 0 < t + q) :
    (∫ u in p..q, (t + u)⁻¹) = Real.log ((t + q) / (t + p)) := by
  have htranslate :=
    intervalIntegral.integral_comp_add_right (fun u : ℝ => u⁻¹) t
      (a := p) (b := q)
  have heq : (fun u : ℝ => (t + u)⁻¹) =
      (fun u : ℝ => (u + t)⁻¹) := by
    funext u
    rw [add_comm]
  rw [heq]
  rw [htranslate]
  simpa [add_comm] using
    integral_inv_of_pos hp hq
end MetricCodes.Spherical.HigherHierarchy
