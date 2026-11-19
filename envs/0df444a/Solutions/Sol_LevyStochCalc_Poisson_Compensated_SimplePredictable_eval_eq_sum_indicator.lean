-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.SimplePredictable.eval_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:56:04.472859+00:00
-- url     : https://prove2.me/submissions/b6f4d327-ff19-41ef-8868-d0f425c8331b

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F000

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [MeasurableSpace E]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (e : E) (ω : Ω) :
    φ.eval s e ω = ∑ i : Fin φ.N,
      (φ.fullRect i).indicator (fun _ : ℝ × E => φ.ξ i ω) (s, e) := by
  unfold SimplePredictable.eval
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (s, e) ∈ φ.fullRect i
  · rw [Set.indicator_of_mem h]
    simp only [SimplePredictable.fullRect, Set.mem_prod, Set.mem_Ioc] at h
    rw [if_pos ⟨h.1.1, h.1.2, h.2⟩]
  · rw [Set.indicator_of_notMem h]
    simp only [SimplePredictable.fullRect, Set.mem_prod, Set.mem_Ioc] at h
    rw [if_neg (fun ⟨h1, h2, h3⟩ => h ⟨⟨h1, h2⟩, h3⟩)]
