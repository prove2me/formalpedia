-- Prove2me | solution 1 for Kyprianou.ProofPreparation.two_poisson_sum_hasLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:40:08.257512+00:00
-- url     : https://prove2.me/submissions/6e2e8b05-5154-474c-b777-0c6aa6b60aed

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r₁ r₂ : ℝ≥0) (X Y : Ω → ℕ)
    (hX : P.map X = poissonMeasure r₁)
    (hY : P.map Y = poissonMeasure r₂)
    (hi : IndepFun X Y P) :
    P.map (fun ω => X ω + Y ω) = poissonMeasure (r₁ + r₂) := by
  have hmX : HasLaw X (poissonMeasure r₁) P := by
    refine ⟨?_, hX⟩
    apply AEMeasurable.of_map_ne_zero
    rw [hX]
    intro heq
    have hp : (poissonMeasure r₁) Set.univ = 1 := measure_univ
    simp [heq] at hp
  have hmY : HasLaw Y (poissonMeasure r₂) P := by
    refine ⟨?_, hY⟩
    apply AEMeasurable.of_map_ne_zero
    rw [hY]
    intro heq
    have hp : (poissonMeasure r₂) Set.univ = 1 := measure_univ
    simp [heq] at hp
  exact (hi.hasLaw_add_poissonMeasure hmX hmY).map_eq
