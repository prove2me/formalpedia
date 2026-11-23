-- Prove2me | solution 1 for Kyprianou.Ch02.finiteIntensityRegionCutoffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:54:07.715354+00:00
-- url     : https://prove2.me/submissions/7977ba21-ea61-4784-8f6c-d4f466f45d4d

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {E ι : Type} [MeasurableSpace E] (m : Measure E) (A : ι → Set E)
    [DecidablePred (fun i => m (A i) < (⊤ : ENNReal))]
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    let B : ι → Set E := fun i => if m (A i) < ⊤ then A i else ∅
    (∀ i, MeasurableSet (B i)) ∧
    (∀ i, m (B i) < ⊤) ∧
    Pairwise (fun i j => Disjoint (B i) (B j)) := by
  dsimp
  constructor
  · intro i
    by_cases hi : m (A i) < ⊤ <;> simp [hi, hA i]
  constructor
  · intro i
    by_cases hi : m (A i) < ⊤ <;> simp [hi]
  · intro i j hij
    by_cases hi : m (A i) < ⊤ <;>
    by_cases hj : m (A j) < ⊤ <;>
    simp [hi, hj, hdisj hij]
