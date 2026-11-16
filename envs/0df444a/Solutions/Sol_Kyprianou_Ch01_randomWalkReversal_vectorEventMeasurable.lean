-- Prove2me | solution 1 for Kyprianou.Ch01.randomWalkReversal_vectorEventMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:35:52.179732+00:00
-- url     : https://prove2.me/submissions/f7d4976b-81a1-42b4-aa0d-b0727df7dd19

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_pathCombinatorics
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem solution
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    let seq : (Fin n → ℝ) → ℕ → ℝ :=
      fun v i => if h : i < n then v ⟨i, h⟩ else 0
    let psum : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => ∑ i ∈ Finset.range j, seq v i
    MeasurableSet {v : Fin n → ℝ |
      psum v n ∈ B ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum v j} := by
  dsimp
  let seq : (Fin n → ℝ) → ℕ → ℝ :=
    fun v i => if h : i < n then v ⟨i, h⟩ else 0
  let psum : (Fin n → ℝ) → ℕ → ℝ :=
    fun v j => ∑ i ∈ Finset.range j, seq v i
  have hpsum (j : ℕ) : Measurable (fun v : Fin n → ℝ => psum v j) := by
    dsimp [psum, seq]
    apply Finset.measurable_sum
    intro i hi
    by_cases h : i < n
    · simpa [h] using (measurable_pi_apply (⟨i, h⟩ : Fin n))
    · simp [h]
  change MeasurableSet {v : Fin n → ℝ |
    psum v n ∈ B ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum v j}
  refine (hB.preimage (hpsum n)).inter ?_
  have hset :
      {v : Fin n → ℝ | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum v j} =
      ⋂ j : ℕ, {v : Fin n → ℝ | 1 ≤ j → j ≤ n → 0 < psum v j} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  change MeasurableSet {v : Fin n → ℝ |
    ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum v j}
  rw [hset]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : 1 ≤ j
  · by_cases hjn : j ≤ n
    · simpa [hj, hjn] using (measurableSet_lt measurable_const (hpsum j))
    · simp [hjn]
  · simp [hj]
