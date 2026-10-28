-- Prove2me | solution 2 for MarkovProcess.map_finTail_pi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:02:30.135004+00:00
-- url     : https://prove2.me/submissions/1f817533-2667-4f9f-8e84-812eebf3000f

import Mathlib

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
theorem solution {n : ℕ} (nu : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (nu i)] :
    (Measure.pi nu).map Fin.tail = Measure.pi (fun i : Fin n ↦ nu i.succ) := by
  have hm : Measurable (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.succ
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : Fin.tail ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (Fin.cons Set.univ s : Fin (n + 1) → Set ℝ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Fin.tail]
    constructor
    · intro h i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa using h j
    · intro h j
      simpa using h j.succ
  rw [this, Measure.pi_pi, Fin.prod_univ_succ]
  simp
