-- Prove2me | solution 1 for MarkovProcess.measurable_finCons
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:46:54.070475+00:00
-- url     : https://prove2.me/submissions/c5003700-5022-417b-a83a-b8226625753f

import Mathlib

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
theorem solution {α : Type*} [MeasurableSpace α] {n : ℕ} :
    Measurable (fun z : α × (Fin n → α) ↦
      @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd
