-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.asymptoticThreshold_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/85d3fd41-ca14-4052-b9e3-ade46e742f9a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_weight_complement_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    MetricCodes.Johnson.asymptoticThreshold d a < 1 := by
  unfold MetricCodes.Johnson.asymptoticThreshold
  have hden : 0 < 2 * a * (1 - a) := by
    exact mul_pos (mul_pos (by norm_num) h.weight_pos)
      h.weight_complement_pos
  have hquot := div_pos h.distance_pos hden
  linarith
end MetricCodes.Johnson.SpectralAsymptotics
