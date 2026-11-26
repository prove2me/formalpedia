-- Prove2me | solution 1 for Kyprianou.Ch04.boundedSquareEnergyDCTV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:37:14.118043+00:00
-- url     : https://prove2.me/submissions/4ee9f76c-5745-417c-886d-1cc6ab056bc1

import Mathlib
open MeasureTheory Filter Topology
set_option autoImplicit false

/-- On a finite measure, uniformly bounded pointwise converging kernels have converging energies. -/
theorem solution {A : Type} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] (g : ℕ → A → ℝ) (h : A → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, |g n x| ≤ K)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (h x))) :
    Tendsto (fun n => ∫ x, (g n x)^2 ∂μ) atTop
      (𝓝 (∫ x, (h x)^2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => K^2)
  · intro n
    exact (hm n).pow 2
  · exact integrable_const _
  · intro n
    filter_upwards [hb n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (g n x), sq_abs (g n x)]
  · filter_upwards [hl] with x hx
    exact hx.pow 2
