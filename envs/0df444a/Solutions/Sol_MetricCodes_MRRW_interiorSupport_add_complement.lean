-- Prove2me | solution 1 for MetricCodes.MRRW.interiorSupport_add_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/dae57aa2-f6a6-464e-8f63-d62e3bc21974

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
theorem _root_.solution (a u e : ℝ) :
    interiorSupport a u e + interiorComplement a u e = e := by
  unfold interiorSupport interiorComplement
  ring
end MetricCodes.MRRW
