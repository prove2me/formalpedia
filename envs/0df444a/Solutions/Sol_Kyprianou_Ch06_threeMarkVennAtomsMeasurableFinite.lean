-- Prove2me | solution 1 for Kyprianou.Ch06.threeMarkVennAtomsMeasurableFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:40:32.741524+00:00
-- url     : https://prove2.me/submissions/e6b69c28-a3c3-4603-88af-7e91a0e94564

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (B C D : Set E) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hFB : n B < ⊤) (hFC : n C < ⊤) (hFD : n D < ⊤) :
    let marks : Fin 7 → Set E := fun i =>
      if i = 0 then (B \ C) \ D
      else if i = 1 then (C \ B) \ D
      else if i = 2 then (D \ B) \ C
      else if i = 3 then (B ∩ C) \ D
      else if i = 4 then (B ∩ D) \ C
      else if i = 5 then (C ∩ D) \ B
      else B ∩ C ∩ D
    ∀ i : Fin 7, MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by
  dsimp only
  intro i
  fin_cases i
  · exact ⟨(hB.diff hC).diff hD,
      lt_of_le_of_lt (measure_mono (by
        intro x hx
        exact hx.1.1)) hFB⟩
  · exact ⟨(hC.diff hB).diff hD,
      lt_of_le_of_lt (measure_mono (by
        intro x hx
        exact hx.1.1)) hFC⟩
  · exact ⟨(hD.diff hB).diff hC,
      lt_of_le_of_lt (measure_mono (by
        intro x hx
        exact hx.1.1)) hFD⟩
  · exact ⟨(hB.inter hC).diff hD,
      lt_of_le_of_lt (measure_mono (by
        intro x hx
        exact hx.1.1)) hFB⟩
  · exact ⟨(hB.inter hD).diff hC,
      lt_of_le_of_lt (measure_mono (by
        intro x hx
        exact hx.1.1)) hFB⟩
  · exact ⟨(hC.inter hD).diff hB,
      lt_of_le_of_lt (measure_mono (by
        intro x hx
        exact hx.1.1)) hFC⟩
  · exact ⟨(hB.inter hC).inter hD,
      lt_of_le_of_lt (measure_mono (by
        intro x hx
        exact hx.1.1)) hFB⟩
