-- Prove2me | solution 1 for MetricCodes.MRRW.rankPenalty_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/945545a2-7321-4fe1-9f61-c1aa49e3037a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution {a u e : ℝ}
    (hweight : 0 < interiorWeight a u e)
    (hweight' : interiorWeight a u e < 1) :
    MetricCodes.Johnson.rankPenalty
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) =
      MetricCodes.binaryEntropy e := by
  have hsupport :
      interiorSupport a u e / interiorWeight a u e = e := by
    unfold interiorSupport
    exact mul_div_cancel_left₀ e hweight.ne'
  have hcomplement :
      interiorComplement a u e / (1 - interiorWeight a u e) = e := by
    unfold interiorComplement
    exact mul_div_cancel_left₀ e (sub_pos.mpr hweight').ne'
  unfold MetricCodes.Johnson.rankPenalty
  rw [hsupport, hcomplement]
  ring
end MetricCodes.MRRW
