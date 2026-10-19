-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.edgeLimit_sq_div_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/657e8afb-3f79-44e2-b97c-4ca7bdb47970

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredDegree_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredWeight_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredDegree_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_sq_sub_eta_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_sigma_sq_sub_degree_sq_pos
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
    edgeLimit a b g u ^ 2 / edgeLimit a 0 0 u =
      hattedEdgeLimit a b g u := by
  rw [edgeLimit_zero_eq h]
  have hzero := zeroFibreParameters h
  have hfactor := hzero.degree_sq_sub_eta_sq_pos
  have hfactor' : 0 < MetricCodes.Johnson.centeredDegree u ^ 2 -
      MetricCodes.Johnson.centeredWeight a ^ 2 := by
    simpa [MetricCodes.Johnson.centeredEta,
      MetricCodes.Johnson.centeredWeight] using hfactor
  have hrad : 0 ≤
      (MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredWeight a ^ 2) *
        (MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredEta a b g ^ 2) *
        (MetricCodes.Johnson.centeredSigma b g ^ 2 -
          MetricCodes.Johnson.centeredDegree u ^ 2) := by
    exact (mul_pos (mul_pos hfactor'
      h.degree_sq_sub_eta_sq_pos)
      h.sigma_sq_sub_degree_sq_pos).le
  have hsquare := Real.sq_sqrt hrad
  have hz := h.centeredDegree_pos.ne'
  have hm := h.one_sub_centeredWeight_sq_pos.ne'
  have hu := h.one_sub_centeredDegree_sq_pos
  have hs := (Real.sqrt_pos.mpr hu).ne'
  have hf := hfactor'.ne'
  unfold edgeLimit hattedEdgeLimit
  field_simp [hz, hm, hs, hf]
  nlinarith [hsquare]
end MetricCodes.Johnson.SpectralAsymptotics
