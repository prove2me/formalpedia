-- Prove2me | solution 1 for ModernOnlineLearning.Classification.eq_8_5
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T04:10:38.233785+00:00
-- url     : https://prove2.me/submissions/d051f76d-39d6-4079-94e4-982d825bdac1

import Theorems.Thm_ModernOnlineLearning_Classification_eq_8_4
set_option autoImplicit false
open ModernOnlineLearning.Classification

theorem solution {d : ℕ} (T : ℕ) (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (hy : ∀ t ∈ Finset.Icc 1 T, y t = -1 ∨ y t = 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ t ∈ Finset.Icc 1 T, ‖z t‖ ≤ R) (u : ModernOnlineLearning.Adaptive.Vec d) :
    mistakes z y T ≤
        ‖u‖ * R * Real.sqrt (mistakes z y T) +
          (∑ t ∈ Finset.Icc 1 T,
            mistakeIndicator z y t * hingePower 1 (inner ℝ (z t) u) (y t)) ∧
      ‖u‖ * R * Real.sqrt (mistakes z y T) +
          (∑ t ∈ Finset.Icc 1 T,
            mistakeIndicator z y t * hingePower 1 (inner ℝ (z t) u) (y t)) ≤
        ‖u‖ * R * Real.sqrt (mistakes z y T) + cumulativeHinge z y T u 1 := by
  have hb := ModernOnlineLearning.Classification.eq_8_4 T z y hy R hR hz u
  have hhinge (t : ℕ) : hingePower 1 (inner ℝ (z t) u) (y t) =
      max (1 - y t * inner ℝ (z t) u) 0 := by simp [hingePower]
  have hτ (t : ℕ) : 0 ≤ mistakeIndicator z y t ∧ mistakeIndicator z y t ≤ 1 := by
    unfold mistakeIndicator; split_ifs <;> norm_num
  constructor
  · have hpoint : ∀ t ∈ Finset.Icc 1 T,
        mistakeIndicator z y t ≤
          mistakeIndicator z y t * y t * inner ℝ (z t) u +
          mistakeIndicator z y t * hingePower 1 (inner ℝ (z t) u) (y t) := by
      intro t ht
      rw [hhinge]
      have h := mul_le_mul_of_nonneg_left (le_max_left (1 - y t * inner ℝ (z t) u) 0) (hτ t).1
      nlinarith
    have hsum := Finset.sum_le_sum hpoint
    rw [Finset.sum_add_distrib] at hsum
    change (∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t) ≤ _
    linarith [hb.1.trans hb.2]
  · apply add_le_add le_rfl
    unfold cumulativeHinge
    apply Finset.sum_le_sum
    intro t ht
    have hp : 0 ≤ hingePower 1 (inner ℝ (z t) u) (y t) := by
      rw [hhinge]; exact le_max_right _ _
    simpa using mul_le_mul_of_nonneg_right (hτ t).2 hp


