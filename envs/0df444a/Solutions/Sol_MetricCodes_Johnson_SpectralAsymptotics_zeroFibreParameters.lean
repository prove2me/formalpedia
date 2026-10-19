-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.zeroFibreParameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/878bea27-f70d-44ad-8364-ce68d5a6d5b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_weight_complement_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_pos

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
    MetricCodes.Johnson.AsymptoticParameters d a 0 0 u := by
  refine ⟨h.distance_pos, h.distance_lt_half,
    h.weight_gt_distance, h.weight_lt_half,
    le_rfl, ?_, le_rfl, ?_, ?_, h.degree_lt_weight, ?_, ?_⟩
  · linarith [h.weight_pos]
  · linarith [h.weight_complement_pos]
  · simpa using h.degree_pos
  · simpa using h.degree_lt_weight
  · nlinarith [h.degree_lt_weight, h.weight_lt_half]
end MetricCodes.Johnson.SpectralAsymptotics
