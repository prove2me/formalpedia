-- Prove2me | solution 2 for MarkovProcess.measurable_finCons
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:47:21.310019+00:00
-- url     : https://prove2.me/submissions/14782b3b-1247-4936-82d9-53d9a6ff1155

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
theorem solution {α : Type*} [MeasurableSpace α] {n : ℕ} :
    Measurable (fun z : α × (Fin n → α) ↦
      @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd
