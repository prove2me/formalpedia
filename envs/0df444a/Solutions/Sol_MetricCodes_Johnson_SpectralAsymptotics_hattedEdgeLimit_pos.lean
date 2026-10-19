-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.hattedEdgeLimit_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/c93b4a21-6b54-494f-9284-72d57816c82e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredDegree_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredWeight_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredDegree_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_sq_sub_eta_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_sigma_sq_sub_degree_sq_pos

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
    0 < hattedEdgeLimit a b g u := by
  unfold hattedEdgeLimit
  have hz := h.centeredDegree_pos
  have hm := h.one_sub_centeredWeight_sq_pos
  have hu := h.one_sub_centeredDegree_sq_pos
  have he := h.degree_sq_sub_eta_sq_pos
  have hs := h.sigma_sq_sub_degree_sq_pos
  positivity
end MetricCodes.Johnson.SpectralAsymptotics
