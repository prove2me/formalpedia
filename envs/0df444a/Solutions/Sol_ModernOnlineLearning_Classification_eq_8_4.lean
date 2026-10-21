-- Prove2me | solution 1 for ModernOnlineLearning.Classification.eq_8_4
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T04:08:07.914857+00:00
-- url     : https://prove2.me/submissions/c36ff081-864a-4e33-835b-0fd9eba2873a

import Definitions.Def_ModernOnlineLearning_Classification_Perceptron
import Theorems.Thm_ModernOnlineLearning_Classification_theorem_2_13
set_option autoImplicit false
open ModernOnlineLearning.Classification

private lemma iter_one {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ) :
    perceptronIter z y 1 = 0 := by simp [perceptronIter]

private lemma iter_step {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d)
    (y : ℕ → ℝ) {t : ℕ} (ht : t ≠ 0) :
    perceptronIter z y (t + 1) = perceptronIter z y t +
      (mistakeIndicator z y t * y t) • z t := by
  change (if t = 0 then 0 else perceptronIter z y t +
    if y t * Real.sign (inner ℝ (z t) (perceptronIter z y t)) ≤ 0 then y t • z t else 0) = _
  rw [if_neg ht]
  unfold mistakeIndicator
  split_ifs <;> simp

private lemma update_nonpos {d : ℕ} (z : ℕ → ModernOnlineLearning.Adaptive.Vec d)
    (y : ℕ → ℝ) (t : ℕ) :
    mistakeIndicator z y t * y t * inner ℝ (z t) (perceptronIter z y t) ≤ 0 := by
  unfold mistakeIndicator
  split_ifs with h
  · simp only [one_mul]
    rcases lt_trichotomy (inner ℝ (z t) (perceptronIter z y t)) 0 with hn | he | hp
    · rw [Real.sign_of_neg hn] at h
      have : 0 ≤ y t := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos this hn.le
    · rw [he, mul_zero]
    · rw [Real.sign_of_pos hp, mul_one] at h
      exact mul_nonpos_of_nonpos_of_nonneg h hp.le
  · simp

private lemma iter_pairing {d : ℕ} (T : ℕ) (z : ℕ → ModernOnlineLearning.Adaptive.Vec d)
    (y : ℕ → ℝ) (u : ModernOnlineLearning.Adaptive.Vec d) :
    inner ℝ (perceptronIter z y (T + 1)) u =
      ∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t * y t * inner ℝ (z t) u := by
  induction T with
  | zero => simp [iter_one]
  | succ n ih =>
    rw [iter_step z y (by omega), inner_add_left, real_inner_smul_left,
      Finset.sum_Icc_succ_top (by omega), ih]

theorem solution {d : ℕ} (T : ℕ) (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (hy : ∀ t ∈ Finset.Icc 1 T, y t = -1 ∨ y t = 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ t ∈ Finset.Icc 1 T, ‖z t‖ ≤ R) (u : ModernOnlineLearning.Adaptive.Vec d) :
    (∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t * y t * inner ℝ (z t) u) ≤
        ‖u‖ * Real.sqrt (∑ t ∈ Finset.Icc 1 T,
          mistakeIndicator z y t * ‖z t‖ ^ 2) ∧
      ‖u‖ * Real.sqrt (∑ t ∈ Finset.Icc 1 T,
          mistakeIndicator z y t * ‖z t‖ ^ 2) ≤
        ‖u‖ * R * Real.sqrt (mistakes z y T) := by
  let g : ℕ → ModernOnlineLearning.Adaptive.Vec d := fun t => -(mistakeIndicator z y t * y t) • z t
  have hrun : ∀ t ∈ Finset.Icc 1 T,
      perceptronIter z y (t + 1) = perceptronIter z y t - (1 : ℝ) • g t := by
    intro t ht
    rw [iter_step z y (by have := (Finset.mem_Icc.mp ht).1; omega)]
    simp [g]
  have hreg := ModernOnlineLearning.Classification.theorem_2_13 T 1 (by norm_num)
    g (perceptronIter z y) hrun 0
  have hsum : 0 ≤ ∑ t ∈ Finset.Icc 1 T, inner ℝ (g t) (perceptronIter z y t - 0) := by
    apply Finset.sum_nonneg
    intro t ht
    simpa [g, real_inner_smul_left] using neg_nonneg.mpr (update_nonpos z y t)
  have hnorm : ∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2 =
      ∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t * ‖z t‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro t ht
    rcases hy t ht with h | h <;> simp [g, mistakeIndicator, h] <;> split_ifs <;> simp
  rw [hnorm] at hreg
  simp only [iter_one, sub_zero, norm_zero, zero_sub, norm_neg, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, zero_add] at hreg
  have hen : ‖perceptronIter z y (T + 1)‖ ^ 2 ≤
      ∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t * ‖z t‖ ^ 2 := by
    simp only [sub_zero] at hsum
    linarith
  have hτ : ∀ t, 0 ≤ mistakeIndicator z y t := by
    intro t; unfold mistakeIndicator; split_ifs <;> norm_num
  have hM : 0 ≤ mistakes z y T := Finset.sum_nonneg (fun t _ => hτ t)
  have hE : 0 ≤ ∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t * ‖z t‖ ^ 2 :=
    Finset.sum_nonneg (fun t _ => mul_nonneg (hτ t) (sq_nonneg _))
  constructor
  · rw [← iter_pairing]
    calc
      inner ℝ (perceptronIter z y (T + 1)) u ≤ ‖perceptronIter z y (T + 1)‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ Real.sqrt (∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t * ‖z t‖ ^ 2) * ‖u‖ :=
        mul_le_mul_of_nonneg_right ((Real.le_sqrt (norm_nonneg _) hE).mpr hen) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · have hEupper : (∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t * ‖z t‖ ^ 2) ≤
        R ^ 2 * mistakes z y T := by
      unfold mistakes
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hz t ht) 2) (hτ t)
    have hsqrt : Real.sqrt (R ^ 2 * mistakes z y T) = R * Real.sqrt (mistakes z y T) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hR]
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEupper) (norm_nonneg u)
    rw [hsqrt] at hh
    nlinarith


