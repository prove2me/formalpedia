-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_discounted_time_integral_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:49:17.943284+00:00
-- url     : https://prove2.me/submissions/1a6d9d42-80bc-44d5-b90b-eac9a24adb3d


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal
/-- Zero-discount convergence. -/
theorem solution :
    ∀ (μ : Measure ℝ≥0) (f : ℝ≥0 → ℝ≥0∞), Measurable f →
      ∀ r : ℕ → ℝ, Antitone r → Tendsto r atTop (nhds 0) →
      Tendsto (fun n => ∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-r n*(t : ℝ))) * f t ∂μ)
        atTop (nhds (∫⁻ t : ℝ≥0, f t ∂μ)) := by
  intro μ f hf r hr hlim
  let g : ℕ → ℝ≥0 → ℝ≥0∞ := fun n t =>
    ENNReal.ofReal (Real.exp (-r n*(t : ℝ))) * f t
  have hm (n : ℕ) : Measurable (g n) := by
    dsimp [g]
    exact (by fun_prop : Measurable (fun t : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-r n*(t : ℝ))))).mul hf
  apply lintegral_tendsto_of_tendsto_of_monotone (fun n => (hm n).aemeasurable)
  · filter_upwards with t i j hij
    change ENNReal.ofReal (Real.exp (-r i*(t : ℝ))) * f t ≤
      ENNReal.ofReal (Real.exp (-r j*(t : ℝ))) * f t
    gcongr
    exact hr hij
  · filter_upwards with t
    have h : Tendsto (fun n => -r n*(t : ℝ)) atTop (nhds (0 : ℝ)) := by
      simpa using hlim.neg.mul (tendsto_const_nhds (x := (t : ℝ)))
    have he := Real.continuous_exp.continuousAt.tendsto.comp h
    have hn : Tendsto (fun n => ENNReal.ofReal (Real.exp (-r n*(t : ℝ))))
        atTop (nhds 1) := by
      simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
    simpa [g] using ENNReal.Tendsto.mul_const (b := f t) hn (Or.inl one_ne_zero)
