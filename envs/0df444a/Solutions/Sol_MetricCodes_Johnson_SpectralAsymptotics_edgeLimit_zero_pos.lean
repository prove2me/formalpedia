-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.edgeLimit_zero_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/2b19b5d5-1b2f-43d8-aebe-20e008a008a1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredDegree_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredWeight_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredDegree_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_sq_sub_eta_sq_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_zeroFibreParameters
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_edgeLimit_zero_eq

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
    0 < edgeLimit a 0 0 u := by
  rw [edgeLimit_zero_eq h]
  have hzero := zeroFibreParameters h
  have hfactor := hzero.degree_sq_sub_eta_sq_pos
  have hfactor' : 0 < MetricCodes.Johnson.centeredDegree u ^ 2 -
      MetricCodes.Johnson.centeredWeight a ^ 2 := by
    simpa [MetricCodes.Johnson.centeredEta,
      MetricCodes.Johnson.centeredWeight] using hfactor
  have hz := h.centeredDegree_pos
  have hm := h.one_sub_centeredWeight_sq_pos
  have hu := h.one_sub_centeredDegree_sq_pos
  positivity
end MetricCodes.Johnson.SpectralAsymptotics
