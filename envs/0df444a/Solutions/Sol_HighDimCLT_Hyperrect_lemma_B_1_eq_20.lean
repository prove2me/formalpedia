-- Prove2me | solution 1 for HighDimCLT.Hyperrect.lemma_B_1_eq_20
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:27:11.349122+00:00
-- url     : https://prove2.me/submissions/70415fff-daa2-4618-ba04-fffc98df9b1a

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ₁ φ₂ : ℝ → ℝ) (hφ₁ : Monotone φ₁) (hφ₂ : Monotone φ₂)
    (hφ₁0 : ∀ x, 0 ≤ φ₁ x) (hφ₂0 : ∀ x, 0 ≤ φ₂ x)
    (ξ₁ ξ₂ : Ω → ℝ) (hξ₁ : Measurable ξ₁) (hξ₂ : Measurable ξ₂)
    (hi₁₁ : Integrable (fun ω => φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω)) P)
    (hi₂₂ : Integrable (fun ω => φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω)) P)
    (hi₁₂ : Integrable (fun ω => φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω)) P) :
    ∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω) ∂P ≤
      (∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P) + ∫ ω, φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω) ∂P := by
  rw [← integral_add hi₁₁ hi₂₂]
  refine integral_mono hi₁₂ (hi₁₁.add hi₂₂) (fun ω => ?_)
  simp only [Pi.add_apply]
  set a := ξ₁ ω
  set b := ξ₂ ω
  have h1 := mul_nonneg (hφ₁0 a) (hφ₂0 a)
  have h2 := mul_nonneg (hφ₁0 b) (hφ₂0 b)
  rcases le_total a b with hab | hab
  · have : φ₁ a * φ₂ b ≤ φ₁ b * φ₂ b :=
      mul_le_mul_of_nonneg_right (hφ₁ hab) (hφ₂0 b)
    linarith
  · have : φ₁ a * φ₂ b ≤ φ₁ a * φ₂ a :=
      mul_le_mul_of_nonneg_left (hφ₂ hab) (hφ₁0 a)
    linarith
