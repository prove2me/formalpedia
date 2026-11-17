-- Prove2me | solution 1 for Kyprianou.Ch06.finiteUnionMarkedIntensityFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:50:33.456637+00:00
-- url     : https://prove2.me/submissions/3f73656d-24a5-43ea-bc27-b8a4cf1849d0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E]
    (n : Measure E) (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ n (B i) < ⊤) :
    MeasurableSet (⋃ i, B i) ∧ n (⋃ i, B i) < ⊤ := by
  constructor
  · exact MeasurableSet.iUnion (fun i => (hB i).1)
  · calc
      n (⋃ i, B i) ≤ ∑ i : Fin m, n (B i) :=
        measure_iUnion_fintype_le n B
      _ < ⊤ := by
        exact ENNReal.sum_lt_top.mpr (fun i hi => (hB i).2)
