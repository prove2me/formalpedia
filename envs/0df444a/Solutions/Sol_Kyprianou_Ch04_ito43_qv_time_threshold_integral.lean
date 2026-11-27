-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_time_threshold_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:26:41.399917+00:00
-- url     : https://prove2.me/submissions/7030f6d5-9f5c-407c-b7e8-e699a9918851

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Evaluate the Lebesgue mass of the threshold tail by interval length. -/
theorem solution
    (t b : NNReal) :
    (∫ s in Ici (b:ℝ) ∩ Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) =
      (∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) -
      (∫ s in Icc (0:ℝ) ((min t b:NNReal):ℝ), (1:ℝ) ∂volume) := by
  have hset : Ici (b:ℝ) ∩ Icc (0:ℝ) (t:ℝ) = Icc (b:ℝ) (t:ℝ) := by
    ext x
    simp only [mem_inter_iff,mem_Ici,mem_Icc]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,b.coe_nonneg.trans h.1,h.2⟩⟩
  have hlen (a d : ℝ) : (∫ _ in Icc a d, (1:ℝ) ∂volume) = max (d-a) 0 := by
    rw [integral_const,measureReal_def,Measure.restrict_apply_univ,
      Real.volume_Icc,ENNReal.toReal_ofReal']
    simp
  rw [hset,hlen,hlen,hlen,sub_zero,sub_zero,max_eq_left t.coe_nonneg,
    max_eq_left (min t b).coe_nonneg]
  by_cases h : b ≤ t
  · rw [min_eq_right h,max_eq_left (sub_nonneg.mpr (show (b:ℝ) ≤ (t:ℝ) from h))]
  · rw [min_eq_left (le_of_not_ge h),sub_self,
      max_eq_right (sub_nonpos.mpr (show (t:ℝ) ≤ (b:ℝ) from le_of_not_ge h))]
