-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparisonMeasure_absolutelyContinuous_arcsineMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/c7c6c9e4-7af9-45b3-b942-54d0b60074f6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_betaMeasure_absolutelyContinuous_betaMeasure

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Entropy
namespace MetricCodes.Spherical.HigherHierarchy.Entropy
theorem _root_.solution :
    comparisonMeasure ≪ arcsineMeasure := by
  have hbeta : betaMeasure 1 (1 / 2) ≪ betaMeasure (1 / 2) (1 / 2) :=
    betaMeasure_absolutelyContinuous_betaMeasure
      (by norm_num) (by norm_num)
  have hscale : MeasurableEmbedding (fun t : ℝ => t / 4) := by
    convert measurableEmbedding_mulRight₀
      (show (4 : ℝ)⁻¹ ≠ 0 by norm_num) using 1
    ext t
    simp [div_eq_mul_inv]
  exact hscale.absolutelyContinuous_map hbeta
end MetricCodes.Spherical.HigherHierarchy.Entropy
