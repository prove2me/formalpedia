-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_logLikelihood_of_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/f676e0cb-d446-4b94-a9e1-b14a97f3d44c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonMeasure_absolutelyContinuous_arcsineMeasure
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonMeasure_ae_mem_Ioo

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
theorem _root_.solution
    (hdensity : comparisonMeasure.rnDeriv arcsineMeasure =ᵐ[arcsineMeasure]
      fun t => ENNReal.ofReal (Real.pi * Real.sqrt t)) :
    llr comparisonMeasure arcsineMeasure =ᵐ[comparisonMeasure]
      fun t => Real.log Real.pi + Real.log t / 2 := by
  have hdensity' := comparisonMeasure_absolutelyContinuous_arcsineMeasure.ae_le hdensity
  filter_upwards [hdensity', comparisonMeasure_ae_mem_Ioo] with t ht htpos
  unfold llr
  rw [ht, ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg _)),
    Real.log_mul Real.pi_pos.ne' (Real.sqrt_pos.mpr htpos.1).ne',
    Real.log_sqrt htpos.1.le]
end MetricCodes.Spherical.HigherHierarchy.Entropy
