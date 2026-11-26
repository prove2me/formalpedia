-- Prove2me | solution 1 for Kyprianou.Ch04.finiteMeasureL2ConvergenceL1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:39:27.848917+00:00
-- url     : https://prove2.me/submissions/61bfb871-4e5b-42d4-9548-e7afb9c00d21

import Mathlib
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
universe u

/-- On a finite measure space convergence of the L2 error implies convergence of the L1 error. -/
theorem solution
    {A : Type u} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (f : ℕ → A → ℝ) (g : A → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ)
    (h₂ : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) := by
  let c : ENNReal := μ Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)
  have hc : c ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · norm_num
    · exact measure_ne_top μ Set.univ
  have hupper : Tendsto (fun n => eLpNorm (f n - g) 2 μ * c) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const h₂ (Or.inr hc)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro n
    exact zero_le
  · intro n
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ENNReal) ≤ 2)
      ((hf n).sub hg)
