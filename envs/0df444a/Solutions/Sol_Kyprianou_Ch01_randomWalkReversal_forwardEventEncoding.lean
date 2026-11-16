-- Prove2me | solution 1 for Kyprianou.Ch01.randomWalkReversal_forwardEventEncoding
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:32:21.899205+00:00
-- url     : https://prove2.me/submissions/b4e5e6f7-6ecb-4119-b960-4d855e0c5fb2

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
        ∀ j : ℕ, 1 ≤ j → j ≤ n →
          0 < ∑ i ∈ Finset.range j, increment i ω) ↔
      (    psum (fun i : Fin n => increment i ω) n ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n →
        0 < psum (fun i : Fin n => increment i ω) j) := by 
  dsimp
  let forward : Ω → Fin n → ℝ := fun ω i => increment i ω
  let seq : (Fin n → ℝ) → ℕ → ℝ :=
    fun v i => if h : i < n then v ⟨i, h⟩ else 0
  let psum : (Fin n → ℝ) → ℕ → ℝ :=
    fun v j => ∑ i ∈ range j, seq v i
  have hforward (ω : Ω) (j : ℕ) (hj : j ≤ n) :
      psum (forward ω) j = ∑ i ∈ range j, increment i ω := by
    dsimp [psum, seq, forward]
    apply sum_congr rfl
    intro i hi
    have hin : i < n := lt_of_lt_of_le (mem_range.mp hi) hj
    simp [hin]
  have hpos (ω : Ω) :
      (psum (forward ω) n ∈ B ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < psum (forward ω) j) ↔
      ((∑ i ∈ range n, increment i ω) ∈ B ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ n →
          0 < ∑ i ∈ range j, increment i ω) := by
    constructor <;> rintro ⟨hb, hp⟩
    · exact ⟨by simpa only [hforward ω n le_rfl] using hb,
        fun j hj hjn => by
          simpa only [hforward ω j hjn] using hp j hj hjn⟩
    · exact ⟨by simpa only [hforward ω n le_rfl] using hb,
        fun j hj hjn => by
          simpa only [hforward ω j hjn] using hp j hj hjn⟩
  exact fun ω => (hpos ω).symm
