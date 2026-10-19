-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.zero_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/69d50339-655d-495f-bdec-5b15571c2488

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zeroAngle_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zeroAngle_le_pi

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
    {N i j : ℕ} (hN : 0 < N) (hj : j ≤ N) (hij : i < j) :
    zero R N j < zero R N i := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  have hangles : zeroAngle N i < zeroAngle N j := by
    unfold zeroAngle
    apply (div_lt_div_iff_of_pos_right hN').2
    exact mul_lt_mul_of_pos_right hij' Real.pi_pos
  unfold zero
  apply mul_lt_mul_of_pos_left _ (by positivity : 0 < R / 2)
  gcongr
  exact Real.cos_lt_cos_of_nonneg_of_le_pi
    (zeroAngle_nonneg N i) (zeroAngle_le_pi hN hj) hangles
end MetricCodes.Spherical.HigherHierarchyChebyshev
