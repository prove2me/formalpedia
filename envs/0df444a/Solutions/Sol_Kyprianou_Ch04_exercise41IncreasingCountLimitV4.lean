-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41IncreasingCountLimitV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:23:44.509794+00:00
-- url     : https://prove2.me/submissions/a298c0ff-7796-4ea5-866c-7feb4682c343

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41CountIntegralV3
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (I : Finset ℕ) (A : ℕ → ℕ → Set Ω) (C : ℝ≥0∞)
    (hm : ∀ m i, i ∈ I → MeasurableSet (A m i))
    (hmono : ∀ i ∈ I, Monotone (fun m => A m i))
    (hbound : ∀ m, ∑ i ∈ I, P (A m i) ≤ C) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ⨆ m : ℕ, ∑ i ∈ I, (A m i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω
    Measurable N ∧ (∫⁻ ω, N ω ∂P) ≤ C := by
  dsimp only
  let f : ℕ → Ω → ℝ≥0∞ := fun m ω =>
    ∑ i ∈ I, (A m i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω
  have hfm (m : ℕ) : Measurable (f m) :=
    (exercise41CountIntegralV3 P I (A m) (fun i hi => hm m i hi)).1
  have hfmono : Monotone f := by
    intro m n hmn ω
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : ω ∈ A m i
    · have h' := hmono i hi hmn h
      simp [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · simp [Set.indicator_of_notMem h]
  change Measurable (fun ω => ⨆ m, f m ω) ∧
    (∫⁻ ω, ⨆ m, f m ω ∂P) ≤ C
  refine ⟨Measurable.iSup hfm, ?_⟩
  rw [lintegral_iSup hfm hfmono]
  refine iSup_le fun m => ?_
  rw [(exercise41CountIntegralV3 P I (A m) (fun i hi => hm m i hi)).2]
  exact hbound m
