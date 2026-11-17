-- Prove2me | solution 1 for Kyprianou.Ch06.nonemptyMarkPatternAtomFiniteIntensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:55:08.707401+00:00
-- url     : https://prove2.me/submissions/9e6495f4-070b-4aa1-b174-47f33668bbdf

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (m : Nat) (B : Fin m → Set E)
    (hFinite : ∀ i : Fin m, n (B i) < ⊤)
    (S : Finset (Fin m)) (i : Fin m) (hi : i ∈ S) :
    n {x : E | ∀ j : Fin m, (x ∈ B j ↔ j ∈ S)} < ⊤ := by
  have hSubset :
      {x : E | ∀ j : Fin m, (x ∈ B j ↔ j ∈ S)} ⊆ B i := by
    intro x hx
    exact (hx i).mpr hi
  exact lt_of_le_of_lt (measure_mono hSubset) (hFinite i)
