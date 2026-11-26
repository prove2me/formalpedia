-- Prove2me | solution 1 for ManyServerQED.Scheduling.coordinate_probability_errors_imply_vector_convergence
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T15:28:27.174194+00:00
-- url     : https://prove2.me/submissions/f105564f-6f35-4f18-8392-7a39266535ff

import Mathlib
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Finset



theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {I : Type*} [Fintype I] (D : ℕ → Ω → I → ℝ)
    (h : ∀ i ε, 0 < ε → Tendsto (fun n => P {ω | ε ≤ |D n ω i|}) atTop (𝓝 0)) :
    TendstoInMeasure P D atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hsum : Tendsto (fun n => ∑ i, P {ω | ε ≤ |D n ω i|}) atTop (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ (fun i _ => h i ε hε)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => bot_le) (fun n => ?_)
  refine (measure_mono ?_).trans (measure_iUnion_fintype_le P _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, sub_zero] at hω
  rw [Set.mem_iUnion]
  by_contra hc
  have : ‖D n ω‖ < ε := (pi_norm_lt_iff hε).mpr (fun i => by
    rw [Real.norm_eq_abs]
    exact lt_of_not_ge (fun hi => hc ⟨i, hi⟩))
  linarith
