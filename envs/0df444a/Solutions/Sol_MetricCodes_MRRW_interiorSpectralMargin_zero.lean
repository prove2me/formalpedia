-- Prove2me | solution 1 for MetricCodes.MRRW.interiorSpectralMargin_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/73a9bb27-d9dc-472c-a8be-e0641debcbd2

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
theorem _root_.solution {δ a u : ℝ}
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    interiorSpectralMargin δ a u 0 = 0 := by
  simp [interiorSpectralMargin, hboundary]
end MetricCodes.MRRW
