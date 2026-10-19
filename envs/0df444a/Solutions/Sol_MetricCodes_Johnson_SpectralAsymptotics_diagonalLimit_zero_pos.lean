-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.diagonalLimit_zero_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/e8dbafdf-ec47-407d-9a20-100ed08d5a95

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
    0 < diagonalLimit a 0 0 u := by
  have hz := h.centeredDegree_pos
  have hm := h.centeredWeight_pos
  have hden := h.one_sub_centeredWeight_sq_pos
  have hu := h.one_sub_centeredDegree_sq_pos
  rw [diagonalLimit_zero_eq h]
  exact div_pos (mul_pos (sq_pos_of_pos hm) hu)
    (mul_pos (sq_pos_of_pos hz) hden)
end MetricCodes.Johnson.SpectralAsymptotics
