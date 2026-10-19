-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Arcsine.betaMeasure_one_half_eq_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/714e94eb-ee78-4c88-95e9-252d1ce4b8f6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_betaPDF_one_half_eq_mul_half_pi_sqrt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Interval
open MetricCodes.Spherical.HigherHierarchy.Arcsine
namespace MetricCodes.Spherical.HigherHierarchy.Arcsine
theorem _root_.solution :
    betaMeasure 1 (1 / 2 : ℝ) =
      (betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).withDensity
        (fun t => ENNReal.ofReal (Real.pi / 2 * Real.sqrt t)) := by
  unfold betaMeasure
  have hbeta : Measurable (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    (measurable_betaPDFReal _ _).ennreal_ofReal
  have hweight :
      Measurable (fun t : ℝ => ENNReal.ofReal (Real.pi / 2 * Real.sqrt t)) := by
    fun_prop
  rw [← withDensity_mul volume hbeta hweight]
  congr 1
  funext t
  exact betaPDF_one_half_eq_mul_half_pi_sqrt t
end MetricCodes.Spherical.HigherHierarchy.Arcsine
