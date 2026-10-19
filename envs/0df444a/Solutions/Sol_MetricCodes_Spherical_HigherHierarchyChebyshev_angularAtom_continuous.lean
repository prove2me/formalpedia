-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularAtom_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/06df65eb-eea2-401d-95a8-9b0f2015c5a9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_spectralAtom_inverseQuadratic
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularQuadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularQuadratic_continuous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    Continuous (angularAtom R) := by
  have hq := angularQuadratic_continuous R
  have hnum : Continuous
      (fun t : ℝ => Real.sqrt (angularQuadratic R t)) :=
    Real.continuous_sqrt.comp hq
  have hden : Continuous
      (fun t : ℝ => Real.sqrt (1 + 4 * angularQuadratic R t)) := by
    fun_prop
  have hdiv := hnum.div hden (fun t => by
    exact (Real.sqrt_pos.mpr
      (by nlinarith [angularQuadratic_nonneg hR.le t])).ne')
  apply hdiv.congr
  intro t
  unfold angularAtom
  exact (spectralAtom_inverseQuadratic
    (angularQuadratic_nonneg hR.le t)).symm
end MetricCodes.Spherical.HigherHierarchyChebyshev
