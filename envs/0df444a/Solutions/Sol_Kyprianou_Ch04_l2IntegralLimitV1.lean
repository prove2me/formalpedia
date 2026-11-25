-- Prove2me | solution 1 for Kyprianou.Ch04.l2IntegralLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:38:06.832823+00:00
-- url     : https://prove2.me/submissions/95e5cd62-8fbe-482e-80ac-708bcc8b82e8

import Mathlib
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- L² convergence on a finite measure space implies convergence of the first moments. -/
theorem solution {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_integral_of_L1' g hg.aestronglyMeasurable
    (Eventually.of_forall fun n => (hf n).integrable (by norm_num))
  have hb (n : ℕ) : eLpNorm (f n - g) 1 μ ≤
      eLpNorm (f n - g) 2 μ * μ univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
      ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable)
  have hc : μ univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ univ)).ne
  have ht := ENNReal.Tendsto.mul_const h (Or.inr hc)
  simp only [zero_mul] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) hb
