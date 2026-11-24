-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_killing_barrier_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:48:45.45765+00:00
-- url     : https://prove2.me/submissions/f6005f7d-d13b-4dd5-a2f3-14a8acd22d47

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_barrier_event_exhaustion
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_barrier_sections_measurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    Tendsto (fun n : ℕ => (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
      P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X (n : ℝ)) 0 ω ∧
        shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue)) atTop (𝓝 (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
      P {ω | shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue)) := by
  let S (t : ℝ≥0) (n : ℕ) : Set Ω :=
    {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X (n : ℝ)) 0 ω ∧
      shifted D.X x t ω ∈ A}
  let d (t : ℝ≥0) := ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
  let f (n : ℕ) (t : ℝ≥0) := d t * P (S t n)
  have hmeas (n : ℕ) : Measurable (f n) := by
    have hd : Measurable d := by dsimp [d]; fun_prop
    exact hd.mul (p2m89_barrier_sections_measurable D ψ W hψ hW q hq x A hA n)
  have hm : Monotone f := by
    intro n m h t
    dsimp [f]
    have hle : P (S t n) ≤ P (S t m) :=
      measure_mono ((p2m89_barrier_event_exhaustion D ψ W hψ hW q hq x A hA t).1 h)
    gcongr
  have hi (t : ℝ≥0) : (⨆ n, f n t) = d t * P {ω | shifted D.X x t ω ∈ A} := by
    obtain ⟨hS, he⟩ := p2m89_barrier_event_exhaustion D ψ W hψ hW q hq x A hA t
    have hlim := tendsto_measure_iUnion_atTop (μ := P) hS
    have heq : (⨆ n, P (S t n)) = P (⋃ n, S t n) :=
      tendsto_nhds_unique (tendsto_atTop_iSup (show Monotone (fun n => P (S t n)) from
        fun n m h => measure_mono (hS h))) hlim
    dsimp [f]
    rw [← ENNReal.mul_iSup, heq, measure_congr he]
  change Tendsto (fun n => ∫⁻ t, f n t ∂positiveTimeLebesgue) atTop
    (𝓝 (∫⁻ t, d t * P {ω | shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue))
  have heq : (⨆ n, ∫⁻ t, f n t ∂positiveTimeLebesgue) =
      ∫⁻ t, d t * P {ω | shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
    rw [← lintegral_iSup hmeas hm]
    exact lintegral_congr hi
  rw [← heq]
  exact tendsto_atTop_iSup (fun n m h => lintegral_mono (hm h))
