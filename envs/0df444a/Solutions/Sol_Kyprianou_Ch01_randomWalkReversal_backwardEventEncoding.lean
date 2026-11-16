-- Prove2me | solution 1 for Kyprianou.Ch01.randomWalkReversal_backwardEventEncoding
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:38:21.572398+00:00
-- url     : https://prove2.me/submissions/e29b482f-2621-4a6f-aa5e-9f1c6c1c0b2a

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkReversal_pathCombinatorics
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (increment : ℕ → Ω → ℝ)
    (n : ℕ) (B : Set ℝ) :
    let seq : (Fin n → ℝ) → ℕ → ℝ :=
      fun v i => if h : i < n then v ⟨i, h⟩ else 0
    let psum : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => ∑ i ∈ Finset.range j, seq v i
    ∀ ω : Ω,
      ((∑ i ∈ Finset.range n, increment i ω) ∈ B ∧
        ∀ j : ℕ, j < n →
          (∑ i ∈ Finset.range j, increment i ω) <
            (∑ i ∈ Finset.range n, increment i ω)) ↔
      (    psum (fun i : Fin n => increment (Fin.rev i) ω) n ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n →
        0 < psum (fun i : Fin n => increment (Fin.rev i) ω) j) := by 
  dsimp
  let backwards : Ω → Fin n → ℝ :=
    fun ω i => increment (Fin.rev i) ω
  let seq : (Fin n → ℝ) → ℕ → ℝ :=
    fun v i => if h : i < n then v ⟨i, h⟩ else 0
  let psum : (Fin n → ℝ) → ℕ → ℝ :=
    fun v j => ∑ i ∈ range j, seq v i
  have hbackwards (ω : Ω) (j : ℕ) (hj : j ≤ n) :
      psum (backwards ω) j =
        ∑ i ∈ range j, increment (n - 1 - i) ω := by
    dsimp [psum, seq, backwards]
    apply sum_congr rfl
    intro i hi
    have hin : i < n := lt_of_lt_of_le (mem_range.mp hi) hj
    have hidx : ((Fin.rev (⟨i, hin⟩ : Fin n)) : ℕ) =
        n - 1 - i := by
      simp only [Fin.val_rev]
      omega
    change n - (i + 1) = n - 1 - i at hidx
    simpa [hin] using
      (congrArg (fun k : ℕ => increment k ω) hidx)
  have hrecord (ω : Ω) :
      ((∑ i ∈ range n, increment i ω) ∈ B ∧
        ∀ j : ℕ, j < n →
          (∑ i ∈ range j, increment i ω) <
            (∑ i ∈ range n, increment i ω)) ↔
      (psum (backwards ω) n ∈ B ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum (backwards ω) j) := by
    have hcomb :=
      Kyprianou.Ch01.randomWalkReversal_pathCombinatorics
        (fun i => increment i ω) n B
    constructor
    · intro h
      rcases hcomb.mp h with ⟨hb, hp⟩
      exact ⟨by simpa only [hbackwards ω n le_rfl] using hb,
        fun j hj hjn => by
          simpa only [hbackwards ω j hjn] using hp j hj hjn⟩
    · rintro ⟨hb, hp⟩
      apply hcomb.mpr
      exact ⟨by simpa only [hbackwards ω n le_rfl] using hb,
        fun j hj hjn => by
          simpa only [hbackwards ω j hjn] using hp j hj hjn⟩
  exact hrecord
