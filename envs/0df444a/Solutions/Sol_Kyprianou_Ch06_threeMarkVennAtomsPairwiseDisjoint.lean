-- Prove2me | solution 1 for Kyprianou.Ch06.threeMarkVennAtomsPairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:40:26.74888+00:00
-- url     : https://prove2.me/submissions/6e3f20b0-4fbf-4e0f-bb1c-89308c7ecc56

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {E : Type} (B C D : Set E) :
    let marks : Fin 7 → Set E := fun i =>
      if i = 0 then (B \ C) \ D
      else if i = 1 then (C \ B) \ D
      else if i = 2 then (D \ B) \ C
      else if i = 3 then (B ∩ C) \ D
      else if i = 4 then (B ∩ D) \ C
      else if i = 5 then (C ∩ D) \ B
      else B ∩ C ∩ D
    ∀ i j : Fin 7, i ≠ j → Disjoint (marks i) (marks j) := by
  dsimp only
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  fin_cases i <;> fin_cases j <;>
    simp_all [Set.mem_diff, Set.mem_inter_iff] <;> tauto
