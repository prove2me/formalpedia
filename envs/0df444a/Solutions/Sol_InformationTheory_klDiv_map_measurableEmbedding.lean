-- Prove2me | solution 1 for InformationTheory.klDiv_map_measurableEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T16:37:21.686469+00:00
-- url     : https://prove2.me/submissions/fafbe6cb-59dc-4a6f-bae5-3a0e7dda0f11

import Theorems.Thm_InformationTheory_klDiv_map_eq_klDiv_trim_comap
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Relative entropy is invariant under a measurable embedding

`klDiv (μ.map f) (ν.map f) = klDiv μ ν` whenever `f` is a measurable embedding.

Pushing two measures forward along an injective measurable map with measurable range loses no
information, so the divergence is unchanged. This is the sharp form of the data-processing
inequality: equality holds exactly when nothing is forgotten.

It specialises Exercise 14.9 (relative entropy between push-forwards, printed p. 195): a
measurable embedding generates the whole σ-algebra, so the trim in that statement is trivial.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem solution {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  -- for an embedding the generated σ-algebra is everything, so the trim does nothing
  have key : ∀ (m : MeasurableSpace α) (hm : m ≤ mα), m = mα →
      @klDiv α m (μ.trim hm) (ν.trim hm) = @klDiv α mα μ ν := by
    rintro m hm rfl
    simp only [trim_eq_self]
  rw [InformationTheory.klDiv_map_eq_klDiv_trim_comap hf.measurable μ ν]
  exact key _ hf.measurable.comap_le hf.comap_eq
