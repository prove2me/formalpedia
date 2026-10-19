-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_entropy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/4e3fe27f-2397-434b-b6be-69e0b52d2e2e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_two_interval
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_rational_log_lower
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_rational_log_upper
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_log_scaled_pow_two

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy.Numerics
namespace MetricCodes.Spherical.HigherHierarchy.Numerics
theorem _root_.solution :
    Phi kissingAmbient kissingStabilizer < (0.396605 : ℝ) := by
  have htwo := MetricCodes.Numerics.log_two_interval.1
  have ha₀plus : Real.log (1 + kissingAmbient 0) < (0.086664734 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₀scale : (0.370525776 : ℝ) < Real.log (16 * kissingAmbient 0) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₁plus : Real.log (1 + kissingAmbient 1) < (0.000565798 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₁scale :
      (0.147626829 : ℝ) < Real.log (2048 * kissingAmbient 1) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₂plus : Real.log (1 + kissingAmbient 2) < (0.000002495 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₂scale :
      (0.268306714 : ℝ) < Real.log (524288 * kissingAmbient 2) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₀plus : (0.006907403 : ℝ) < Real.log (1 + kissingStabilizer 0) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₀scale :
      Real.log (256 * kissingStabilizer 0) < (0.573471664 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₁plus :
      (0.000043804 : ℝ) < Real.log (1 + kissingStabilizer 1) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₁scale :
      Real.log (32768 * kissingStabilizer 1) < (0.361459204 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hmain :
      (1 + kissingAmbient 0) * Real.log (1 + kissingAmbient 0) -
          kissingAmbient 0 *
            (Real.log (16 * kissingAmbient 0) - 4 * Real.log 2) +
        ((1 + kissingAmbient 1) * Real.log (1 + kissingAmbient 1) -
          kissingAmbient 1 *
            (Real.log (2048 * kissingAmbient 1) - 11 * Real.log 2)) +
        ((1 + kissingAmbient 2) * Real.log (1 + kissingAmbient 2) -
          kissingAmbient 2 *
            (Real.log (524288 * kissingAmbient 2) - 19 * Real.log 2)) -
        ((1 + kissingStabilizer 0) * Real.log (1 + kissingStabilizer 0) -
          kissingStabilizer 0 *
            (Real.log (256 * kissingStabilizer 0) - 8 * Real.log 2)) -
        ((1 + kissingStabilizer 1) * Real.log (1 + kissingStabilizer 1) -
          kissingStabilizer 1 *
            (Real.log (32768 * kissingStabilizer 1) - 15 * Real.log 2)) <
          (0.396605 : ℝ) * Real.log 2 := by
    norm_num at htwo ha₀plus ha₀scale ha₁plus ha₁scale ha₂plus ha₂scale hb₀plus hb₀scale hb₁plus hb₁scale ⊢
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    Phi kissingAmbient kissingStabilizer =
      ((1 + kissingAmbient 0) * Real.log (1 + kissingAmbient 0) -
          kissingAmbient 0 * Real.log (kissingAmbient 0) +
        ((1 + kissingAmbient 1) * Real.log (1 + kissingAmbient 1) -
          kissingAmbient 1 * Real.log (kissingAmbient 1)) +
        ((1 + kissingAmbient 2) * Real.log (1 + kissingAmbient 2) -
          kissingAmbient 2 * Real.log (kissingAmbient 2)) -
        ((1 + kissingStabilizer 0) * Real.log (1 + kissingStabilizer 0) -
          kissingStabilizer 0 * Real.log (kissingStabilizer 0)) -
        ((1 + kissingStabilizer 1) * Real.log (1 + kissingStabilizer 1) -
          kissingStabilizer 1 * Real.log (kissingStabilizer 1))) /
            Real.log 2 := by
      unfold Phi
      rw [Fin.sum_univ_three, Fin.sum_univ_two]
      unfold MetricCodes.sphericalEntropy Real.logb
      ring
    _ < (0.396605 : ℝ) := by
      apply (div_lt_iff₀ hlog).2
      rw [log_scaled_pow_two (u := kissingAmbient 0) (by norm_num) 4,
        log_scaled_pow_two (u := kissingAmbient 1) (by norm_num) 11,
        log_scaled_pow_two (u := kissingAmbient 2) (by norm_num) 19,
        log_scaled_pow_two (u := kissingStabilizer 0) (by norm_num) 8,
        log_scaled_pow_two (u := kissingStabilizer 1) (by norm_num) 15]
      norm_num at hmain ⊢
      exact hmain
end MetricCodes.Spherical.HigherHierarchy.Numerics
