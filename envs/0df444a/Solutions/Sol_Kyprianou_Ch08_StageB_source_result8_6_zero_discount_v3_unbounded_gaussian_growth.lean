-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_gaussian_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:00:23.219162+00:00
-- url     : https://prove2.me/submissions/c7d45555-72cf-4262-a213-8a08d4905132

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
noncomputable section

theorem solution
    (μ : Measure ℝ) (d a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧ ∀ θ : ℝ, β ≤ θ →
      C < d + a * θ +
        (∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ) - B / θ := by
  intro C
  let M : ℝ := C - d + B + 1
  refine ⟨max 1 (M / a), le_max_left _ _, ?_⟩
  intro θ hθβ
  have hθone : 1 ≤ θ := (le_max_left 1 (M / a)).trans hθβ
  have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one hθone
  have hdiv : M / a ≤ θ := (le_max_right 1 (M / a)).trans hθβ
  have hMθ : M ≤ a * θ := by
    have hh := (div_le_iff₀ ha).1 hdiv
    nlinarith
  have hBdiv : B / θ ≤ B := by
    apply (div_le_iff₀ hθpos).2
    simpa using mul_le_mul_of_nonneg_left hθone hB
  have hJ : 0 ≤ ∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ := by
    apply integral_nonneg
    intro y
    have hr : 0 ≤ Real.exp (θ * y) - 1 - θ * y := by
      linarith [Real.add_one_le_exp (θ * y)]
    exact div_nonneg hr hθpos.le
  dsimp [M] at hMθ
  linarith
