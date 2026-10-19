-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.pole_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/e1b7b8dc-daed-4545-80d8-633ffd82ab44

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_poleAngle_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_poleAngle_lt_pi

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    0 < pole R N i := by
  have hcos : -1 < Real.cos (poleAngle N i) := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi
      (poleAngle_pos hN i).le (le_refl Real.pi) (poleAngle_lt_pi hN hi)
  unfold pole
  exact mul_pos (by positivity) (by linarith)
end MetricCodes.Spherical.HigherHierarchyChebyshev
