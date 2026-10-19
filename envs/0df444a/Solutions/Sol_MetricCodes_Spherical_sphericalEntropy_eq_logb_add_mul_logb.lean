-- Prove2me | solution 1 for MetricCodes.Spherical.sphericalEntropy_eq_logb_add_mul_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/f78fe10f-472f-4663-b5e9-232da7e287d6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {a : ℝ} (ha : 0 < a) :
    MetricCodes.sphericalEntropy a =
      Real.logb 2 (1 + a) + a * Real.logb 2 ((1 + a) / a) := by
  unfold MetricCodes.sphericalEntropy
  rw [Real.logb_div (by positivity) ha.ne']
  ring
end MetricCodes.Spherical
