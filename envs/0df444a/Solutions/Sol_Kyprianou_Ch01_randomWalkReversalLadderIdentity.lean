-- Prove2me | solution 1 for Kyprianou.Ch01.randomWalkReversalLadderIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:43:41.694168+00:00
-- url     : https://prove2.me/submissions/2a98e2cf-6bbb-4751-ae6c-a5e0290f47d2

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_vectorEventMeasurable
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_forwardEventEncoding
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_backwardEventEncoding
import Theorems.Thm_Kyprianou_Ch01_randomWalkIID_reversal_eventProbability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

/-- Deterministic path reversal plus iid finite-vector event invariance. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ i : ℕ, Measurable (increment i))
    (hindep : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hLaw : ∀ i : ℕ, HasLaw (increment i) jumpLaw P) :
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    ∀ (n : ℕ), 1 ≤ n →
      ∀ B : Set ℝ, MeasurableSet B →
        P {ω | S n ω ∈ B ∧
          ∀ j : ℕ, j < n → S j ω < S n ω} =
        P {ω | S n ω ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω} := by
  dsimp
  intro n hn B hB
  let forward : Ω → Fin n → ℝ := fun ω i => increment i ω
  let backwards : Ω → Fin n → ℝ :=
    fun ω i => increment (Fin.rev i) ω
  let seq : (Fin n → ℝ) → ℕ → ℝ :=
    fun v i => if h : i < n then v ⟨i, h⟩ else 0
  let psum : (Fin n → ℝ) → ℕ → ℝ :=
    fun v j => ∑ i ∈ range j, seq v i
  let E : Set (Fin n → ℝ) :=
    {v | psum v n ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum v j}
  have hE : MeasurableSet E :=
    Kyprianou.Ch01.randomWalkReversal_vectorEventMeasurable n B hB
  have hrecord :=
    Kyprianou.Ch01.randomWalkReversal_backwardEventEncoding increment n B
  have hpos :=
    Kyprianou.Ch01.randomWalkReversal_forwardEventEncoding increment n B
  have heq :=
    Kyprianou.Ch01.randomWalkIID_reversal_eventProbability
      P increment hmeas hindep jumpLaw hLaw n E hE
  calc
    P {ω | (∑ i ∈ range n, increment i ω) ∈ B ∧
      ∀ j : ℕ, j < n →
        (∑ i ∈ range j, increment i ω) <
          (∑ i ∈ range n, increment i ω)} =
      P {ω | backwards ω ∈ E} := by
        congr 1
        ext ω
        exact hrecord ω
    _ = P {ω | forward ω ∈ E} := heq.symm
    _ = P {ω | (∑ i ∈ range n, increment i ω) ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n →
        0 < ∑ i ∈ range j, increment i ω} := by
        congr 1
        ext ω
        exact (hpos ω).symm
