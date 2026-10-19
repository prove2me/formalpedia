-- Prove2me | solution 1 for MetricCodes.MRRW.interiorSpectralMargin_derivative_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/f6781e19-4f06-47ec-a357-b93b4d8852ce

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
theorem _root_.solution
    {a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2) :
    0 <
      (1 - 2 * (a * (1 - a))) *
          (1 - 2 * Real.sqrt (u * (1 - u))) /
        (a * (1 - a) * Real.sqrt (u * (1 - u)) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
  have ha0 : 0 < a := lt_trans hu hua
  have ha1 : 0 < 1 - a := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu hu1)
  have hvariance : u * (1 - u) < (1 : ℝ) / 4 := by
    nlinarith [sq_pos_of_pos (by linarith : 0 < 1 - 2 * u)]
  have hshalf : Real.sqrt (u * (1 - u)) < (1 : ℝ) / 2 := by
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by nlinarith)
  have hweight : 0 < 1 - 2 * (a * (1 - a)) := by
    nlinarith [sq_nonneg (a - (1 : ℝ) / 2)]
  exact div_pos
    (mul_pos hweight (by linarith))
    (by positivity)
end MetricCodes.MRRW
