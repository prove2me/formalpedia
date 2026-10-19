-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.spectralGap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/a5f25846-d886-4015-a7e1-e87d0f2bdb86

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (h : MetricCodes.Johnson.Feasible d a b g u) :
    0 < spectralGap d a b g u := by
  have hgap :
      MetricCodes.Johnson.asymptoticThreshold d a <
        MetricCodes.Johnson.spectralLimit a b g u := h.2
  unfold spectralGap
  linarith
end MetricCodes.Johnson.SpectralAsymptotics
