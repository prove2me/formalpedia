-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicPositiveJumpLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:14:38.853086+00:00
-- url     : https://prove2.me/submissions/0e8554e7-251a-425a-b398-60b91fd320e9

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpPMFExists
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ jump : PMF ℕ,
      (∀ n : ℕ, jump n =
        ENNReal.ofReal
          ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q)))) ∧
      IsProbabilityMeasure
        (jump.toMeasure.map (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) ∧
      (jump.toMeasure.map (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) {0} = 0 := by
  obtain ⟨jump, hjump⟩ :=
    Kyprianou.Ch01.logarithmicJumpPMFExists q hq0 hq1
  refine ⟨jump, hjump, ?_, ?_⟩
  · letI : IsProbabilityMeasure jump.toMeasure := inferInstance
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  · have hmeas : Measurable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
      fun_prop
    rw [Measure.map_apply hmeas (measurableSet_singleton (0 : ℝ))]
    have hempty :
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) ⁻¹' ({0} : Set ℝ) = ∅ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      have hn : n + 1 ≠ 0 := by omega
      exact_mod_cast hn
    rw [hempty]
    exact measure_empty
