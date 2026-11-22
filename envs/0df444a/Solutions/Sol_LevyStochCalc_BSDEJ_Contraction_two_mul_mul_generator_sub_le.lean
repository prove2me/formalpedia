-- Prove2me | solution 1 for LevyStochCalc.BSDEJ.Contraction.two_mul_mul_generator_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:48:04.742355+00:00
-- url     : https://prove2.me/submissions/4f9bb651-fa17-4af2-86ad-e919d7d04e3d

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

variable {d : ℕ} {E : Type*} [MeasurableSpace E] {ν : Measure E}
variable {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

theorem solution {β : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) (a : ℝ) :
    2 * (a * (f s y₁ z₁ u₁ - f s y₂ z₂ u₂))
      ≤ β / 2 * a ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
  classical
  let I : ℝ≥0∞ := ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν
  let g := f s y₁ z₁ u₁ - f s y₂ z₂ u₂
  let y := y₁ - y₂
  let z := z₁ - z₂
  let S : ℝ := ∑ j, (z₁ j - z₂ j) ^ 2
  change 2 * (a * g) ≤ β / 2 * a ^ 2 + 6 * L ^ 2 / β * (y ^ 2 + S + I.toReal)
  have hpow : I ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hu
  have hbound := hlip s y₁ y₂ z₁ z₂ u₁ u₂
  change (‖g‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
    ((‖y‖₊ : ℝ≥0∞) + (‖z‖₊ : ℝ≥0∞) + I ^ (1 / 2 : ℝ)) at hbound
  have hr := ENNReal.toReal_mono (by finiteness) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL, ENNReal.toReal_add (by simp) hpow,
    ENNReal.toReal_add (by simp) (by simp), ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow] at hr
  change ‖g‖ ≤ L * (‖y‖ + ‖z‖ + √I.toReal) at hr
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hz : ‖z‖ ≤ √S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hS, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (f := fun j : Fin d => (z₁ j - z₂ j) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hzs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hz
  rw [Real.sq_sqrt hS] at hzs
  have hthree : (‖y‖ + ‖z‖ + √I.toReal)^2 ≤ 3 * (y^2 + S + I.toReal) := by
    have hy : ‖y‖ ^ 2 = y ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (‖y‖ - ‖z‖), sq_nonneg (‖z‖ - √I.toReal),
      sq_nonneg (‖y‖ - √I.toReal), Real.sq_sqrt I.toReal_nonneg]
  have hsq := (sq_le_sq₀ (norm_nonneg g) (by positivity)).mpr hr
  rw [Real.norm_eq_abs, sq_abs, mul_pow] at hsq
  have hgen := hsq.trans (mul_le_mul_of_nonneg_left hthree (sq_nonneg L))
  have hw : 2 * (a * g) ≤ β / 2 * a ^ 2 + 2 / β * g ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hβ).mp
    field_simp
    nlinarith [sq_nonneg (β * a - 2 * g)]
  calc
    _ ≤ _ := hw
    _ ≤ β / 2 * a ^ 2 + (2 / β) * (L ^ 2 * (3 * (y ^ 2 + S + I.toReal))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hgen (show 0 ≤ 2 / β by positivity))
    _ = _ := by ring

#print axioms solution
