-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedUnitBoxes_subset_region
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:57.40723+00:00
-- url     : https://prove2.me/submissions/924a14b0-0d50-4aac-83d6-9b487033f270

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution {m : Nat} (w : Fin m → Real) (B : Real)
    (hw : ∀ i, 0 < w i) :
    (⋃ a ∈ OAI.PiExponent.realWeightedSimplex w B,
      {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) ⊆
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧
        ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i} := by
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
  obtain ⟨a, ha, hx⟩ := hx
  have hB : ∑ i, w i * (a i : ℝ) ≤ B := by
    unfold OAI.PiExponent.realWeightedSimplex at ha
    exact (Finset.mem_filter.1 ha).2
  refine ⟨fun i => le_trans (Nat.cast_nonneg _) (hx i).1, ?_⟩
  have : ∑ i, w i * x i ≤ ∑ i, (w i * (a i : ℝ) + w i) :=
    Finset.sum_le_sum fun i _ => by nlinarith [hx i, hw i]
  rw [Finset.sum_add_distrib] at this
  linarith
