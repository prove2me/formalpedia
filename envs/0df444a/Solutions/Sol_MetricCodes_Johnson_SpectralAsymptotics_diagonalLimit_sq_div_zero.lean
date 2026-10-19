-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.diagonalLimit_sq_div_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/dfd3a01c-7fd2-4bff-bd91-558cc28db670

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredDegree_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredWeight_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredWeight_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredDegree_sq_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_diagonalLimit_zero_eq

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
    diagonalLimit a b g u ^ 2 / diagonalLimit a 0 0 u =
      hattedDiagonalLimit a b g u := by
  have hz := h.centeredDegree_pos.ne'
  have hm := h.centeredWeight_pos.ne'
  have hd := h.one_sub_centeredWeight_sq_pos.ne'
  have hu := h.one_sub_centeredDegree_sq_pos.ne'
  rw [diagonalLimit_zero_eq h]
  unfold diagonalLimit hattedDiagonalLimit
  field_simp [hz, hm, hd, hu]
end MetricCodes.Johnson.SpectralAsymptotics
