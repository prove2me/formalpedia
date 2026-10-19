-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_relativeEntropy_eq_log_pi_sub_one_of_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/ee158082-62f4-459f-96ca-fca03e5906bd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonMeasure_absolutelyContinuous_arcsineMeasure
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_logLikelihood_of_density

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
      fun t => ENNReal.ofReal (Real.pi * Real.sqrt t))
    (hlog : Integrable (fun t : ℝ => Real.log t) comparisonMeasure)
    (hmoment : (∫ t, Real.log t ∂comparisonMeasure) = -2) :
    (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal =
      Real.log Real.pi - 1 := by
  rw [InformationTheory.toReal_klDiv_of_measure_eq
    comparisonMeasure_absolutelyContinuous_arcsineMeasure (by simp)]
  rw [integral_congr_ae (comparison_logLikelihood_of_density hdensity)]
  rw [integral_add (integrable_const _) (hlog.div_const 2),
    integral_const, probReal_univ, one_smul, integral_div, hmoment]
  ring
end MetricCodes.Spherical.HigherHierarchy.Entropy
