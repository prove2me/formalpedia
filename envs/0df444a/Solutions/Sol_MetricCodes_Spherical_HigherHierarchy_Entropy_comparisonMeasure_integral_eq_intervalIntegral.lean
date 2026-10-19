-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparisonMeasure_integral_eq_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/f8617975-db01-4917-beab-e60756847d87

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonLebesgueDensity_measurable
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonMeasure_eq_volume_withDensity

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
theorem _root_.solution (f : ℝ → ℝ) :
    (∫ t, f t ∂comparisonMeasure) =
      ∫ t in (0 : ℝ)..(1 / 4 : ℝ),
        f t / Real.sqrt (1 / 4 - t) := by
  rw [comparisonMeasure_eq_volume_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      comparisonLebesgueDensity_measurable (by
        filter_upwards [] with t
        unfold comparisonLebesgueDensity
        split_ifs <;> simp),
    intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) (1 / 4)
  · have ht' : 0 < t ∧ t < (1 / 4 : ℝ) := ht
    change (comparisonLebesgueDensity t).toReal * f t =
      (Set.Ioo (0 : ℝ) (1 / 4)).indicator
        (fun t => f t / Real.sqrt (1 / 4 - t)) t
    rw [comparisonLebesgueDensity, if_pos ht', Set.indicator_of_mem ht,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  · have ht' : ¬ (0 < t ∧ t < (1 / 4 : ℝ)) := by simpa using ht
    change (comparisonLebesgueDensity t).toReal * f t =
      (Set.Ioo (0 : ℝ) (1 / 4)).indicator
        (fun t => f t / Real.sqrt (1 / 4 - t)) t
    rw [comparisonLebesgueDensity, if_neg ht',
      Set.indicator_of_notMem ht]
    simp
end MetricCodes.Spherical.HigherHierarchy.Entropy
