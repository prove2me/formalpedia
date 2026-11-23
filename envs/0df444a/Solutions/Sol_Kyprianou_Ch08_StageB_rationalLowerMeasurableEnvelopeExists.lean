-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.rationalLowerMeasurableEnvelopeExists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:01:36.335076+00:00
-- url     : https://prove2.me/submissions/039457f4-3500-47db-acf5-c57a446b7c84

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ℝ → Set Ω) :
    ∃ B : ℝ → Set Ω,
      (∀ y : ℝ, MeasurableSet (B y)) ∧
      Monotone B ∧
      (∀ y : ℝ, ∀ ω : Ω, ω ∈ B y →
        ∃ h : ℝ, h < y ∧ ω ∈ B h) ∧
      (∀ y : ℝ, ∀ ω : Ω,
        ω ∈ B y ↔
          ∃ r : ℚ, (r : ℝ) < y ∧
            ω ∈ toMeasurable P (A (r : ℝ))) := by
  classical
  let B : ℝ → Set Ω := fun y =>
    ⋃ r : ℚ, {ω | (r : ℝ) < y ∧
      ω ∈ toMeasurable P (A (r : ℝ))}
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro y
    change MeasurableSet (⋃ r : ℚ,
      {ω | (r : ℝ) < y ∧ ω ∈ toMeasurable P (A (r : ℝ))})
    apply MeasurableSet.iUnion
    intro r
    by_cases h : (r : ℝ) < y
    · simpa [h] using measurableSet_toMeasurable P (A (r : ℝ))
    · simp [h]
  · intro a b hab ω hω
    obtain ⟨r, hra, hrMem⟩ := Set.mem_iUnion.mp hω
    exact Set.mem_iUnion.mpr
      ⟨r, lt_of_lt_of_le hra hab, hrMem⟩
  · intro y ω hω
    obtain ⟨r, hry, hrMem⟩ := Set.mem_iUnion.mp hω
    let h : ℝ := ((r : ℝ) + y) / 2
    have hrh : (r : ℝ) < h := by dsimp [h]; linarith
    have hhy : h < y := by dsimp [h]; linarith
    exact ⟨h, hhy, Set.mem_iUnion.mpr ⟨r, hrh, hrMem⟩⟩
  · intro y ω
    change (ω ∈ ⋃ r : ℚ,
      {z | (r : ℝ) < y ∧ z ∈ toMeasurable P (A (r : ℝ))}) ↔ _
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
