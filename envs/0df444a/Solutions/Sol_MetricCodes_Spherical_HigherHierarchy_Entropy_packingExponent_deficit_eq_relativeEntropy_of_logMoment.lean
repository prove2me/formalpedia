-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.packingExponent_deficit_eq_relativeEntropy_of_logMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/cca5ff59-43c5-4701-a2c5-d73287b46012

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonMeasure_absolutelyContinuous_arcsineMeasure
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_logLikelihood_integrable
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_relativeEntropy_eq_log_pi_sub_one
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_log_integrable_of_logMoment
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_packingExponent_deficit_eq_relativeEntropy

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
    {Γ Φ : ℝ} {K : ℝ → ℝ}
    (hlogMoment : (∫ t, Real.log t ∂comparisonMeasure) = -2)
    (hphase : Integrable K comparisonMeasure)
    (htilt : Integrable (fun t => Real.exp (-K t)) arcsineMeasure)
    (hnormalizer : phaseNormalizer K = 1 - 2 * Γ)
    (hphaseMoment : (∫ t, K t ∂comparisonMeasure) =
      2 * Real.log 2 * Φ) :
    limitingPackingExponent - packingObjective Γ Φ =
      (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal /
        (2 * Real.log 2) := by
  have hlog := comparison_log_integrable_of_logMoment hlogMoment
  exact packingExponent_deficit_eq_relativeEntropy
    comparisonMeasure_absolutelyContinuous_arcsineMeasure hphase htilt
    (comparison_logLikelihood_integrable hlog)
    (comparison_relativeEntropy_eq_log_pi_sub_one hlog hlogMoment)
    hnormalizer hphaseMoment
end MetricCodes.Spherical.HigherHierarchy.Entropy
