-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.arcsine_integral_self_div_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/df26f0b2-c3e0-4ed8-aa38-29e8f7f40f5a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_betaMap_half_half_ae_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_arcsine_stieltjes_integrable
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_arcsine_integral_x_div_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Interval Topology
open MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
namespace MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    (∫ t, t / (t + x) ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        1 - Real.sqrt (x / (x + 1 / 4)) := by
  by_cases hzero : x = 0
  · subst x
    calc
      (∫ t, t / (t + 0) ∂(betaMeasure (1 / 2 : ℝ)
        (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)) =
          ∫ _t : ℝ, 1 ∂(betaMeasure (1 / 2 : ℝ)
            (1 / 2 : ℝ)).map (fun t : ℝ => t / 4) := by
            apply integral_congr_ae
            filter_upwards [betaMap_half_half_ae_pos] with t ht
            simp [ht.ne']
      _ = 1 - Real.sqrt (0 / (0 + 1 / 4)) := by norm_num
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    calc
      (∫ t, t / (t + x) ∂(betaMeasure (1 / 2 : ℝ)
        (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)) =
          ∫ t, (1 - x / (x + t)) ∂(betaMeasure (1 / 2 : ℝ)
            (1 / 2 : ℝ)).map (fun t : ℝ => t / 4) := by
            apply integral_congr_ae
            filter_upwards [betaMap_half_half_ae_pos] with t ht
            have hden : x + t ≠ 0 := ne_of_gt (by linarith)
            field_simp
            ring
      _ = 1 - (∫ t, x / (x + t) ∂(betaMeasure (1 / 2 : ℝ)
            (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)) := by
            rw [integral_sub (integrable_const _)
              (arcsine_stieltjes_integrable hx)]
            rw [integral_const]
            have hprob : IsProbabilityMeasure
                ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
                  (fun t : ℝ => t / 4)) :=
              betaMap_half_half_isProbabilityMeasure
            letI := hprob
            simp only [smul_eq_mul, mul_one, measureReal_def]
            rw [measure_univ]
            norm_num
      _ = 1 - Real.sqrt (x / (x + 1 / 4)) := by
            rw [arcsine_integral_x_div_add hxpos]
end MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
