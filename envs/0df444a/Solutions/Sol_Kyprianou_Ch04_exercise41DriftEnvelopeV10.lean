-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41DriftEnvelopeV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:44.288235+00:00
-- url     : https://prove2.me/submissions/585e3282-675f-4da5-bba9-189c1431ba93

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (X : ℝ → ℝ) (hX : Measurable X) (t R K : ℝ)
    (hXt : ∀ s ∈ Icc (0 : ℝ) t, |X s| ≤ R)
    (g : ℕ → ℝ → ℝ) (D : ℝ → ℝ)
    (hg : ∀ n, ContDiff ℝ 1 (g n))
    (hD : ∀ x, Tendsto (fun n => deriv (g n) x) atTop (𝓝 (D x)))
    (hBound : ∀ n x, |x| ≤ R → ‖deriv (g n) x‖ ≤ K) :
    let μ := (volume : Measure ℝ).restrict (Icc 0 t)
    (∀ n, AEStronglyMeasurable (fun s => deriv (g n) (X s)) μ) ∧
    Integrable (fun _ : ℝ => K) μ ∧
    (∀ n, ∀ᵐ s ∂μ, ‖deriv (g n) (X s)‖ ≤ K) ∧
    (∀ᵐ s ∂μ, Tendsto (fun n => deriv (g n) (X s)) atTop (𝓝 (D (X s)))) := by
  let μ := (volume : Measure ℝ).restrict (Icc 0 t)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top)
  refine ⟨fun n => ((hg n).continuous_deriv_one.measurable.comp hX).aestronglyMeasurable,
    integrable_const K, ?_, Eventually.of_forall (fun s => hD (X s))⟩
  intro n
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Icc (a := 0) (b := t))]
    with s hs
  exact hBound n (X s) (hXt s hs)
