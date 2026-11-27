-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_jump_threshold_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:26:41.5625+00:00
-- url     : https://prove2.me/submissions/19e2f75d-a169-4673-90f3-44bfcc59694c

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Identify the strictly later jump interval with the difference of nested measurable rectangles. -/
theorem solution
    (μ : Measure (ℝ × ℝ)) (t b : NNReal)
    (hi : IntegrableOn (fun z : ℝ × ℝ => z.2^2/2)
      (Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)) μ) :
    (∫ z in {z : ℝ × ℝ | (b:ℝ) < z.1} ∩
        (Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)), z.2^2/2 ∂μ) =
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), z.2^2/2 ∂μ) -
      (∫ z in Icc (0:ℝ) ((min t b:NNReal):ℝ) ×ˢ (univ : Set ℝ), z.2^2/2 ∂μ) := by
  let S : Set (ℝ × ℝ) := Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)
  let R : Set (ℝ × ℝ) := Icc (0:ℝ) ((min t b:NNReal):ℝ) ×ˢ (univ : Set ℝ)
  have hS : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  have hR : MeasurableSet R := measurableSet_Icc.prod MeasurableSet.univ
  have hsub : R ⊆ S := by
    intro z hz
    exact ⟨⟨hz.1.1,hz.1.2.trans (show ((min t b:NNReal):ℝ) ≤ (t:ℝ)
      from min_le_left t b)⟩,hz.2⟩
  have heq : {z : ℝ × ℝ | (b:ℝ) < z.1} ∩ S = S \ R := by
    ext z
    simp only [S,R,mem_inter_iff,mem_setOf_eq,mem_prod,mem_Icc,mem_univ,
      and_true,mem_diff]
    change ((b:ℝ) < z.1 ∧ 0 ≤ z.1 ∧ z.1 ≤ (t:ℝ)) ↔
      (0 ≤ z.1 ∧ z.1 ≤ (t:ℝ)) ∧ ¬ (0 ≤ z.1 ∧ z.1 ≤ min (t:ℝ) (b:ℝ))
    constructor
    · rintro ⟨hb,h0,ht⟩
      exact ⟨⟨h0,ht⟩,fun h => (not_le_of_gt hb) (h.2.trans (min_le_right _ _))⟩
    · rintro ⟨⟨h0,ht⟩,hn⟩
      refine ⟨?_,h0,ht⟩
      by_contra h
      exact hn ⟨h0,le_min ht (le_of_not_gt h)⟩
  change (∫ z in {z : ℝ × ℝ | (b:ℝ) < z.1} ∩ S, z.2^2/2 ∂μ) =
    (∫ z in S, z.2^2/2 ∂μ) - (∫ z in R, z.2^2/2 ∂μ)
  rw [heq]
  apply setIntegral_diff <;> assumption
