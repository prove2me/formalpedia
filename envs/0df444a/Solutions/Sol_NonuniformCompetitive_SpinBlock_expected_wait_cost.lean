-- Prove2me | solution 1 for NonuniformCompetitive.SpinBlock.expected_wait_cost
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:35:21.815252+00:00
-- url     : https://prove2.me/submissions/4e7ef839-ca76-41c4-b757-8c4df9fb3a10

import Definitions.Def_NonuniformCompetitive_SpinBlock_Model

open NonuniformCompetitive.SpinBlock MeasureTheory Set
open scoped NNReal ENNReal

namespace SpinProof

theorem waitCost_measurable (C : ℝ) (τ : ℝ≥0) : Measurable (fun b => waitCost C b τ) := by
  exact measurable_const.ite (measurableSet_Ici) (measurable_id.add_const _)

theorem min_cost_integral (ν : Measure ℝ≥0∞) (τ : ℝ≥0) :
    ∫⁻ b, min b (τ : ℝ≥0∞) ∂ν = ∫⁻ t in Ioc (0:ℝ) τ, ν (Ici (ENNReal.ofReal t)) := by
  have hne (b : ℝ≥0∞) : min b (τ : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hm : Measurable (fun b : ℝ≥0∞ => (min b (τ : ℝ≥0∞)).toReal) :=
    (measurable_id.min measurable_const).ennreal_toReal
  have hc := lintegral_eq_lintegral_meas_le ν
    (Filter.Eventually.of_forall (fun b : ℝ≥0∞ => ENNReal.toReal_nonneg)) hm.aemeasurable
  simp only [ENNReal.ofReal_toReal (hne _)] at hc
  rw [hc]
  have he : (fun t : ℝ => ν {b : ℝ≥0∞ | t ≤ (min b (τ : ℝ≥0∞)).toReal}) =
      (Iic (τ : ℝ)).indicator (fun t => ν (Ici (ENNReal.ofReal t))) := by
    funext t
    by_cases ht : t ≤ τ
    · rw [indicator_of_mem (show t ∈ Iic (τ : ℝ) from ht)]
      congr 1
      ext b
      rw [mem_setOf_eq,mem_Ici,← ENNReal.ofReal_le_iff_le_toReal (hne b),le_min_iff]
      have hτ : ENNReal.ofReal t ≤ (τ : ℝ≥0∞) := by
        exact (ENNReal.ofReal_le_ofReal ht).trans_eq (by simp)
      simp [hτ]
    · rw [indicator_of_notMem (show t ∉ Iic (τ : ℝ) from ht)]
      have hs : {b : ℝ≥0∞ | t ≤ (min b (τ : ℝ≥0∞)).toReal} = ∅ := by
        ext b
        simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
        have h : (min b (τ : ℝ≥0∞)).toReal ≤ (τ : ℝ) := by
          simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (min_le_right b (τ : ℝ≥0∞))
        exact not_le.mpr (h.trans_lt (not_le.mp ht))
      rw [hs,measure_empty]
  rw [he,lintegral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  rw [show Iic (τ : ℝ) ∩ Ioi (0:ℝ) = Ioc (0:ℝ) (τ:ℝ) by ext t; simp [and_comm]]

theorem expected_cost (C : ℝ) (ν : Measure ℝ≥0∞) (τ : ℝ≥0) :
    ∫⁻ b, waitCost C b τ ∂ν = ν (Iio (τ : ℝ≥0∞))*ENNReal.ofReal C +
      ∫⁻ t in Ioc (0:ℝ) τ, ν (Ici (ENNReal.ofReal t)) := by
  have he (b : ℝ≥0∞) : waitCost C b τ =
      min b (τ : ℝ≥0∞)+(Iio (τ : ℝ≥0∞)).indicator (fun _ => ENNReal.ofReal C) b := by
    by_cases hb : (τ : ℝ≥0∞) ≤ b
    · simp [waitCost,hb,min_eq_right hb,not_lt.mpr hb]
    · have h := not_le.mp hb
      simp [waitCost,hb,min_eq_left h.le,h]
  simp_rw [he]
  rw [lintegral_add_left (show Measurable (fun b : ℝ≥0∞ => min b (τ : ℝ≥0∞)) from measurable_id.min measurable_const),
    lintegral_indicator_const measurableSet_Iio,min_cost_integral]
  ac_rfl

end SpinProof

theorem solution (C : ℝ) (hC : 0 < C) (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν] (τ : ℝ≥0) :
    ∫⁻ b, waitCost C b τ ∂ν = ν (Iio (τ : ℝ≥0∞))*ENNReal.ofReal C +
      ∫⁻ t in Ioc (0:ℝ) τ, ν (Ici (ENNReal.ofReal t)) :=
  SpinProof.expected_cost C ν τ
