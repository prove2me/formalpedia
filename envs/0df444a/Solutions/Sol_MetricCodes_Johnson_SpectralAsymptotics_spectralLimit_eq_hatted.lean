-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.spectralLimit_eq_hatted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/8b0261bd-f7db-468d-95f7-cef3a0cca403

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredDegree_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredWeight_sq_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_one_sub_centeredDegree_sq_pos

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
    MetricCodes.Johnson.spectralLimit a b g u =
      hattedDiagonalLimit a b g u + 2 * hattedEdgeLimit a b g u := by
  unfold MetricCodes.Johnson.spectralLimit hattedDiagonalLimit hattedEdgeLimit
  dsimp
  have hz := h.centeredDegree_pos.ne'
  have hm := h.one_sub_centeredWeight_sq_pos.ne'
  have hu := h.one_sub_centeredDegree_sq_pos.ne'
  have hs := (Real.sqrt_pos.mpr h.one_sub_centeredDegree_sq_pos).ne'
  field_simp [hz, hm, hu, hs]
end MetricCodes.Johnson.SpectralAsymptotics
