-- Prove2me | solution 1 for Kyprianou.Ch06.threeMarkVennAtomsAllOutsideA
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:40:38.418617+00:00
-- url     : https://prove2.me/submissions/fc64cefe-ba44-4275-9b3f-6152d32914dd

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {E : Type} (A B C D : Set E)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D) :
    let marks : Fin 7 → Set E := fun i =>
      if i = 0 then (B \ C) \ D
      else if i = 1 then (C \ B) \ D
      else if i = 2 then (D \ B) \ C
      else if i = 3 then (B ∩ C) \ D
      else if i = 4 then (B ∩ D) \ C
      else if i = 5 then (C ∩ D) \ B
      else B ∩ C ∩ D
    ∀ i : Fin 7, Disjoint A (marks i) := by
  dsimp only
  intro i
  fin_cases i
  · apply hAB.mono_right
    intro x hx
    exact hx.1.1
  · apply hAC.mono_right
    intro x hx
    exact hx.1.1
  · apply hAD.mono_right
    intro x hx
    exact hx.1.1
  · apply hAB.mono_right
    intro x hx
    exact hx.1.1
  · apply hAB.mono_right
    intro x hx
    exact hx.1.1
  · apply hAC.mono_right
    intro x hx
    exact hx.1.1
  · apply hAB.mono_right
    intro x hx
    exact hx.1.1
