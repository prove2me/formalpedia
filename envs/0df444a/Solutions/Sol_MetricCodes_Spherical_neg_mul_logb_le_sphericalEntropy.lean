-- Prove2me | solution 1 for MetricCodes.Spherical.neg_mul_logb_le_sphericalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/08c24f3d-e53e-48c0-b3c1-fb2ccd0abe16

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
theorem _root_.solution {b : ℝ} (hb : 0 ≤ b) :
    b * (-Real.logb 2 b) ≤ MetricCodes.sphericalEntropy b := by
  have hlog : 0 ≤ Real.logb 2 (1 + b) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hterm : 0 ≤ (1 + b) * Real.logb 2 (1 + b) := by
    exact mul_nonneg (by linarith) hlog
  unfold MetricCodes.sphericalEntropy
  nlinarith
end MetricCodes.Spherical
