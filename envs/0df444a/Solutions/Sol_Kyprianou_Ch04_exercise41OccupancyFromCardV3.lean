-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41OccupancyFromCardV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:07:02.777108+00:00
-- url     : https://prove2.me/submissions/0a6dad22-6101-4acf-b219-911d3855c46d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteEventSumBoundV1
import Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulIndicatorSumV3
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : Finset ℕ) (A B : ℕ → Set Ω) (p : ℝ≥0∞)
    (hB : ∀ i ∈ I, MeasurableSet (B i))
    (hfactor : ∀ i ∈ I, p * P (A i) ≤ P (B i))
    (hcard : ∀ ω, (I.filter (fun i => ω ∈ B i)).card ≤ 2) :
    p * ∑ i ∈ I, P (A i) ≤ 2 := by
  apply exercise41FiniteEventSumBoundV1 P I A B p hB hfactor
  intro ω
  rw [exercise41SuccessfulIndicatorSumV3]
  exact_mod_cast hcard ω
