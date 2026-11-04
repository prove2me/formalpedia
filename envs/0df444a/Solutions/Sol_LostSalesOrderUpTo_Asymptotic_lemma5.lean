-- Prove2me | solution 1 for LostSalesOrderUpTo.Asymptotic.lemma5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:20:32.633888+00:00
-- url     : https://prove2.me/submissions/a1f53150-c3c3-4dbc-889a-4892ab7230d8

import Theorems.Thm_LostSalesOrderUpTo_Asymptotic_newsvendor_optimal

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

open LostSalesOrderUpTo.Asymptotic

/-- Lemma 5, with both holding-cost denominators explicitly positive. -/
theorem solution (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h b ν : ℝ) (hh : 0 < h) (hb : 0 < b) (hν : 0 < ν)
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ)
    (hhold_b : 0 < expectedHolding μ (newsvendorLevel μ h b))
    (hhold_νb : 0 < expectedHolding μ (newsvendorLevel μ h (ν * b))) :
    (1 + shortageHoldingRatio μ h (ν * b) (newsvendorLevel μ h (ν * b))) /
        (1 + (1 / ν) * shortageHoldingRatio μ h (ν * b)
          (newsvendorLevel μ h (ν * b))) =
      backorderOptimalCost μ h (ν * b) /
        backorderCost μ h b (newsvendorLevel μ h (ν * b)) ∧
    backorderOptimalCost μ h (ν * b) /
        backorderCost μ h b (newsvendorLevel μ h (ν * b)) ≤
      backorderOptimalCost μ h (ν * b) / backorderOptimalCost μ h b ∧
    backorderOptimalCost μ h (ν * b) / backorderOptimalCost μ h b ≤
      backorderCost μ h (ν * b) (newsvendorLevel μ h b) /
        backorderOptimalCost μ h b ∧
    backorderCost μ h (ν * b) (newsvendorLevel μ h b) /
        backorderOptimalCost μ h b =
      (1 + ν * shortageHoldingRatio μ h b (newsvendorLevel μ h b)) /
        (1 + shortageHoldingRatio μ h b (newsvendorLevel μ h b)) := by
  have hshort (S : ℝ≥0) : 0 ≤ expectedShortfall μ S :=
    integral_nonneg (fun _ ↦ le_max_right _ _)
  have hholding (S : ℝ≥0) : 0 ≤ expectedHolding μ S :=
    integral_nonneg (fun _ ↦ le_max_right _ _)
  have hcost (β : ℝ) (hβ : 0 ≤ β) (S : ℝ≥0) : 0 ≤ backorderCost μ h β S :=
    add_nonneg (mul_nonneg hh.le (hholding S)) (mul_nonneg hβ (hshort S))
  have hopt_le (β : ℝ) (hβ : 0 ≤ β) (S : ℝ≥0) :
      backorderOptimalCost μ h β ≤ backorderCost μ h β S := by
    apply csInf_le
    · exact ⟨0, by rintro _ ⟨T, rfl⟩; exact hcost β hβ T⟩
    · exact ⟨S, rfl⟩
  have hνb : 0 < ν * b := mul_pos hν hb
  have hmin_b := newsvendor_optimal μ h b hh hb hmean
  have hmin_νb := newsvendor_optimal μ h (ν * b) hh hνb hmean
  have hpos_b : 0 < backorderOptimalCost μ h b := by
    rw [← hmin_b]
    exact add_pos_of_pos_of_nonneg (mul_pos hh hhold_b)
      (mul_nonneg hb.le (hshort _))
  have hpos_νb : 0 < backorderOptimalCost μ h (ν * b) := by
    rw [← hmin_νb]
    exact add_pos_of_pos_of_nonneg (mul_pos hh hhold_νb)
      (mul_nonneg hνb.le (hshort _))
  have hcross : 0 < backorderCost μ h b (newsvendorLevel μ h (ν * b)) :=
    add_pos_of_pos_of_nonneg (mul_pos hh hhold_νb)
      (mul_nonneg hb.le (hshort _))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmin_νb]
    unfold shortageHoldingRatio backorderCost
    have hden : 0 < h * expectedHolding μ (newsvendorLevel μ h (ν * b)) +
        b * expectedShortfall μ (newsvendorLevel μ h (ν * b)) := hcross
    have hH := mul_pos hh hhold_νb
    have hE := mul_nonneg hb.le (hshort (newsvendorLevel μ h (ν * b)))
    field_simp
    <;> ring
  · exact div_le_div_of_nonneg_left hpos_νb.le hpos_b (hopt_le b hb.le _)
  · exact div_le_div_of_nonneg_right (hopt_le (ν * b) hνb.le _) hpos_b.le
  · rw [← hmin_b]
    unfold shortageHoldingRatio backorderCost
    have hden : 0 < h * expectedHolding μ (newsvendorLevel μ h b) +
        b * expectedShortfall μ (newsvendorLevel μ h b) := by
      change 0 < backorderCost μ h b (newsvendorLevel μ h b)
      rw [hmin_b]
      exact hpos_b
    have hH := mul_pos hh hhold_b
    have hE := mul_nonneg hb.le (hshort (newsvendorLevel μ h b))
    field_simp
    <;> ring


