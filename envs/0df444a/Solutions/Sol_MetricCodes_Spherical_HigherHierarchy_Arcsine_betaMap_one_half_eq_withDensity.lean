-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Arcsine.betaMap_one_half_eq_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/66052e40-004e-4b67-8038-f7b75206921e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_betaMeasure_one_half_eq_withDensity
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_map_withDensity_comp

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
    (betaMeasure 1 (1 / 2 : ℝ)).map (fun t : ℝ => t / 4) =
      ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
        (fun t : ℝ => t / 4)).withDensity
        (fun t => ENNReal.ofReal (Real.pi * Real.sqrt t)) := by
  rw [betaMeasure_one_half_eq_withDensity]
  have hcomp :
      (fun t : ℝ => ENNReal.ofReal (Real.pi / 2 * Real.sqrt t)) =
        (fun t => ENNReal.ofReal (Real.pi * Real.sqrt t)) ∘
          (fun t : ℝ => t / 4) := by
    funext t
    congr 1
    change Real.pi / 2 * Real.sqrt t = Real.pi * Real.sqrt (t / 4)
    rw [Real.sqrt_div' t (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    ring
  rw [hcomp]
  apply map_withDensity_comp
  · fun_prop
  · fun_prop
end MetricCodes.Spherical.HigherHierarchy.Arcsine
