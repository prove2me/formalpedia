-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.strict_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/b5454274-42cb-4e23-a1c3-202d33231324

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zeroAngle_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_poleAngle_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zeroAngle_le_pi
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zeroAngle_lt_poleAngle
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_poleAngle_lt_succ_zeroAngle
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
    zero R N (i + 1) < pole R N i ∧ pole R N i < zero R N i := by
  have hscale : 0 < R / 2 := by positivity
  constructor
  · unfold pole zero
    apply mul_lt_mul_of_pos_left _ hscale
    gcongr
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (poleAngle_pos hN i).le
      (zeroAngle_le_pi hN (Nat.succ_le_of_lt hi))
      (poleAngle_lt_succ_zeroAngle hN)
  · unfold pole zero
    apply mul_lt_mul_of_pos_left _ hscale
    gcongr
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (zeroAngle_nonneg N i)
      (poleAngle_lt_pi hN hi).le
      (zeroAngle_lt_poleAngle hN)
end MetricCodes.Spherical.HigherHierarchyChebyshev
