-- Prove2me | solution 1 for Kyprianou.Ch01.expDensityIoiTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:01:55.698464+00:00
-- url     : https://prove2.me/submissions/608b2100-b128-47ea-afcd-c458e39dc2d2

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution (beta : ℝ) (hbeta : 0 < beta)
    (a : ℝ) (ha : 0 ≤ a) :
    (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun e : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * e))))
      (Set.Ioi a)).toReal = Real.exp (-beta * a) := by
  have hdist : (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun e : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * e))) =
      expMeasure beta := by
    change (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun e : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * e))) =
        volume.withDensity (exponentialPDF beta)
    rw [← withDensity_indicator measurableSet_Ioi]
    apply withDensity_congr_ae
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simpa using (volume_singleton (a := (0 : ℝ)))
    filter_upwards [h0] with x hx
    rw [exponentialPDF_eq]
    by_cases hpos : 0 < x
    · simp [Set.indicator_of_mem hpos, if_pos hpos.le]
      intro hle
      exact False.elim (not_le_of_gt hpos hle)
    · have hneg : x < 0 := by
        rcases lt_trichotomy x 0 with h | h | h
        · exact h
        · exact False.elim (hx h)
        · exact False.elim (hpos h)
      simp [Set.indicator_of_notMem hpos, if_neg (not_le.mpr hneg)]
      intro hp
      exact False.elim (hpos hp)
  rw [hdist]
  haveI := isProbabilityMeasure_expMeasure hbeta
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have h := cdf_expMeasure_eq hbeta a
  rw [cdf_eq_real, if_pos ha] at h
  simp only [Measure.real] at h
  rw [h]
  ring
