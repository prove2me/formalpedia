-- Prove2me | solution 1 for MetricCodes.Johnson.Rate.certificateConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/22dfa304-a812-4f2a-ad67-7cd89789ca8c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_spectralGap_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_spectralGap_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_asymptoticThreshold_lt_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Rate
open MetricCodes.Johnson.Asymptotics
open MetricCodes.Johnson.SpectralAsymptotics
namespace MetricCodes.Johnson.Rate
theorem _root_.solution
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u) :
    0 < certificateConstant d a b g u := by
  unfold certificateConstant
  apply div_pos
  · linarith [asymptoticThreshold_lt_one h.1]
  · exact spectralGap_pos h
end MetricCodes.Johnson.Rate
