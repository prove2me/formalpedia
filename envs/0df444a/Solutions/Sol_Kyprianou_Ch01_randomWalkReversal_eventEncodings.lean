-- Prove2me | solution 1 for Kyprianou.Ch01.randomWalkReversal_eventEncodings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:40:32.411702+00:00
-- url     : https://prove2.me/submissions/c5d4f0a0-c178-443d-98f7-b18325b1bf74

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_vectorEventMeasurable
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_forwardEventEncoding
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_backwardEventEncoding
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*}
    (increment : ℕ → Ω → ℝ) (n : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let forward : Ω → Fin n → ℝ := fun ω i => increment i ω
    let backwards : Ω → Fin n → ℝ := fun ω i => increment (Fin.rev i) ω
    let seq : (Fin n → ℝ) → ℕ → ℝ :=
      fun v i => if h : i < n then v ⟨i, h⟩ else 0
    let psum : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => ∑ i ∈ Finset.range j, seq v i
    let E : Set (Fin n → ℝ) :=
      {v | psum v n ∈ B ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum v j}
    MeasurableSet E ∧
      (∀ ω : Ω,
        ((∑ i ∈ Finset.range n, increment i ω) ∈ B ∧
          ∀ j : ℕ, j < n →
            (∑ i ∈ Finset.range j, increment i ω) <
              (∑ i ∈ Finset.range n, increment i ω)) ↔
          backwards ω ∈ E) ∧
      (∀ ω : Ω,
        ((∑ i ∈ Finset.range n, increment i ω) ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ n →
            0 < ∑ i ∈ Finset.range j, increment i ω) ↔
          forward ω ∈ E) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · exact Kyprianou.Ch01.randomWalkReversal_vectorEventMeasurable n B hB
  · exact Kyprianou.Ch01.randomWalkReversal_backwardEventEncoding increment n B
  · exact Kyprianou.Ch01.randomWalkReversal_forwardEventEncoding increment n B
