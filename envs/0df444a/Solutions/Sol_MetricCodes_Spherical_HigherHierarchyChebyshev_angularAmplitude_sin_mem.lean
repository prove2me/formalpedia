-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularAmplitude_sin_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/f10b8ccd-ed48-4edb-85e0-1f3d6deea01b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularAmplitude_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularAmplitude_lt_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R) (t : ℝ) :
    -(1 : ℝ) < angularAmplitude R * Real.sin (Real.pi * t / 2) ∧
      angularAmplitude R * Real.sin (Real.pi * t / 2) < 1 := by
  have ha := angularAmplitude_pos hR
  have ha' := angularAmplitude_lt_one hR
  have hsin := Real.neg_one_le_sin (Real.pi * t / 2)
  have hsin' := Real.sin_le_one (Real.pi * t / 2)
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hsin ha.le,
    mul_le_mul_of_nonneg_left hsin' ha.le]
end MetricCodes.Spherical.HigherHierarchyChebyshev
