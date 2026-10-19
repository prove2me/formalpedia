-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.packingExponent_deficit_eq_relativeEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/490c0071-17c4-4f4c-8334-0bf0a2eef59d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_phaseNormalizer_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_phase_relativeEntropy_eq_base_add_phase
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_limitingPackingExponent_sub_packingObjective_eq

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
theorem _root_.solution {Γ Φ : ℝ} {K : ℝ → ℝ}
    (hac : comparisonMeasure ≪ arcsineMeasure)
    (hphase : Integrable K comparisonMeasure)
    (htilt : Integrable (fun t => Real.exp (-K t)) arcsineMeasure)
    (hllr : Integrable (llr comparisonMeasure arcsineMeasure) comparisonMeasure)
    (hbase : (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal =
      Real.log Real.pi - 1)
    (hnormalizer : phaseNormalizer K = 1 - 2 * Γ)
    (hphaseMoment : (∫ t, K t ∂comparisonMeasure) =
      2 * Real.log 2 * Φ) :
    limitingPackingExponent - packingObjective Γ Φ =
      (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal /
        (2 * Real.log 2) := by
  have hpositive := phaseNormalizer_pos htilt
  rw [limitingPackingExponent_sub_packingObjective_eq hpositive hnormalizer]
  rw [phase_relativeEntropy_eq_base_add_phase hac hphase htilt hllr,
    hbase, hphaseMoment]
end MetricCodes.Spherical.HigherHierarchy.Entropy
