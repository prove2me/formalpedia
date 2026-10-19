-- Prove2me | solution 1 for MetricCodes.Spherical.classical_geometric_logarithm_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/bf956dc8-0cbd-4f53-bd63-2cb4f0831ffe

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - s)) -
        Real.logb 2 (1 + MetricCodes.classicalThreshold s) =
      Real.logb 2
        (2 * Real.sqrt (2 * (1 + s)) /
          (1 + Real.sqrt (1 - s ^ 2))) := by
  let u : ℝ := Real.sqrt (1 - s ^ 2)
  let v : ℝ := Real.sqrt (2 * (1 + s))
  let a : ℝ := MetricCodes.classicalThreshold s
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hu : 0 < u := Real.sqrt_pos.mpr hrad
  have hu_sq : u ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hrad.le
  have hv : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hv_sq : v ^ 2 = 2 * (1 + s) :=
    Real.sq_sqrt (by positivity)
  have ha : 0 < a := MetricCodes.classicalThreshold_pos hs hs'
  have hplus : 1 + a = (1 + u) / (2 * u) := by
    dsimp [a, u]
    unfold MetricCodes.classicalThreshold
    field_simp
    ring
  have hfactor :
      (2 : ℝ) / (1 - s) =
        (2 * v / (1 + u) * (1 + a)) ^ 2 := by
    rw [hplus]
    field_simp [hu.ne', (by linarith : 1 - s ≠ 0),
      (by positivity : 1 + u ≠ 0)]
    nlinarith [hu_sq, hv_sq]
  have hfirst : 2 * v / (1 + u) ≠ 0 := by positivity
  have hsecond : 1 + a ≠ 0 := by positivity
  change (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - s)) -
    Real.logb 2 (1 + a) = Real.logb 2 (2 * v / (1 + u))
  rw [hfactor, Real.logb_pow,
    Real.logb_mul hfirst hsecond]
  ring
end MetricCodes.Spherical
