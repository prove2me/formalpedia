-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41PassLimitV7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:17:06.683949+00:00
-- url     : https://prove2.me/submissions/7ef5ffef-c294-43d8-b1ae-e2139bf7d9b5

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    {ι : Type} (μ : Measure ℝ)
    (g : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (x0 xt d : ℝ) (D : ℕ → ℝ → ℝ) (D0 : ℝ → ℝ)
    (J : ℕ → ι → ℝ) (J0 : ι → ℝ) (K : ℝ → ℝ) (B : ι → ℝ)
    (h0 : Tendsto (fun n => g n x0) atTop (𝓝 (G x0)))
    (ht : Tendsto (fun n => g n xt) atTop (𝓝 (G xt)))
    (hm : ∀ n, AEStronglyMeasurable (D n) μ)
    (hK : Integrable K μ)
    (hDb : ∀ n, ∀ᵐ s ∂μ, ‖D n s‖ ≤ K s)
    (hDl : ∀ᵐ s ∂μ, Tendsto (fun n => D n s) atTop (𝓝 (D0 s)))
    (hB : Summable B)
    (hJl : ∀ k, Tendsto (fun n => J n k) atTop (𝓝 (J0 k)))
    (hJb : ∀ᶠ n in atTop, ∀ k, ‖J n k‖ ≤ B k)
    (hEq : ∀ n, g n xt = g n x0 +
      d * (∫ s, D n s ∂μ) + ∑' k, J n k) :
    G xt = G x0 + d * (∫ s, D0 s ∂μ) + ∑' k, J0 k := by
  have hI := tendsto_integral_of_dominated_convergence K hm hK hDb hDl
  have hJ := tendsto_tsum_of_dominated_convergence hB hJl hJb
  have hR := (h0.add ((tendsto_const_nhds (x := d)).mul hI)).add hJ
  have he : (fun n => g n xt) =
      (fun n => g n x0 + d * (∫ s, D n s ∂μ) + ∑' k, J n k) :=
    funext hEq
  rw [he] at ht
  exact tendsto_nhds_unique ht hR
