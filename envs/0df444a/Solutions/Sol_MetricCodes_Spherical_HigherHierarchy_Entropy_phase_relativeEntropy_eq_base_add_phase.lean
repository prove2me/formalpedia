-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.phase_relativeEntropy_eq_base_add_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/59f2718a-9bbe-4887-8b60-6390ca5244b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_toReal_klDiv_tilted_eq

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
theorem _root_.solution {K : ℝ → ℝ}
    (hac : comparisonMeasure ≪ arcsineMeasure)
    (hphase : Integrable K comparisonMeasure)
    (htilt : Integrable (fun t => Real.exp (-K t)) arcsineMeasure)
    (hllr : Integrable (llr comparisonMeasure arcsineMeasure) comparisonMeasure) :
    (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal =
      (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal +
        (∫ t, K t ∂comparisonMeasure) + Real.log (phaseNormalizer K) := by
  have h := toReal_klDiv_tilted_eq comparisonMeasure arcsineMeasure
    hac hphase.neg htilt hllr
  change (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal =
    (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal -
      (∫ x, -K x ∂comparisonMeasure) +
        Real.log (∫ x, Real.exp (-K x) ∂arcsineMeasure) at h
  rw [integral_neg] at h
  simpa [phaseNormalizer] using h
end MetricCodes.Spherical.HigherHierarchy.Entropy
