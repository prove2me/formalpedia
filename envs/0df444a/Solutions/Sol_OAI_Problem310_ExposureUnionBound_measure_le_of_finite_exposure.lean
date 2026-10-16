-- Prove2me | solution 1 for OAI.Problem310.ExposureUnionBound.measure_le_of_finite_exposure
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T05:09:02.878974+00:00
-- url     : https://prove2.me/submissions/1ecad176-0946-4904-ae2c-4776b39fad46

-- Proof from OpenAI/math contributors, ExposureUnionBound.lean lines 14–50,
-- commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
-- Standalone adaptation and verification by Codex, directed by
-- Alexander Richard Towell (queelius). No new mathematical argument claimed.
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

universe u_Ω u_A
open MeasureTheory
open scoped BigOperators

theorem solution
    {Ω : Type u_Ω} {A : Type u_A} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → A) (hf : ∀ a, MeasurableSet {ω | f ω = a})
    (E : Set Ω) (good : Set A) (badBound goodBound : ENNReal)
    (hbad : μ {ω | f ω ∉ good} ≤ badBound)
    (hgood : ∀ a ∈ good,
      μ (E ∩ {ω | f ω = a}) ≤ goodBound * μ {ω | f ω = a}) :
    μ E ≤ badBound + goodBound := by
  classical
  let localEvent : A → Set Ω := fun a =>
    if a ∈ good then E ∩ {ω | f ω = a} else ∅
  have hcover : E ⊆ {ω | f ω ∉ good} ∪ ⋃ a, localEvent a := by
    intro ω hω
    by_cases hg : f ω ∈ good
    · right
      exact Set.mem_iUnion.mpr ⟨f ω, by simp [localEvent, hg, hω]⟩
    · exact Or.inl hg
  have hlocal (a : A) : μ (localEvent a) ≤ goodBound * μ {ω | f ω = a} := by
    by_cases ha : a ∈ good
    · simpa [localEvent, ha] using hgood a ha
    · simp [localEvent, ha]
  have hmass : (∑ a : A, μ {ω | f ω = a}) = 1 := by
    have h := sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset A)
      (f := f) (fun a _ => hf a)
    simpa [Set.preimage] using h
  calc
    μ E ≤ μ ({ω | f ω ∉ good} ∪ ⋃ a, localEvent a) := measure_mono hcover
    _ ≤ μ {ω | f ω ∉ good} + μ (⋃ a, localEvent a) := measure_union_le _ _
    _ ≤ badBound + ∑ a : A, μ (localEvent a) :=
      add_le_add hbad (measure_iUnion_fintype_le μ localEvent)
    _ ≤ badBound + ∑ a : A, goodBound * μ {ω | f ω = a} :=
      add_le_add le_rfl (Finset.sum_le_sum fun a _ => hlocal a)
    _ = badBound + goodBound := by rw [← Finset.mul_sum, hmass, mul_one]
