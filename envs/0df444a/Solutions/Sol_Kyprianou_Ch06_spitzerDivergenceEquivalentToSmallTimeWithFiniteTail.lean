-- Prove2me | solution 1 for Kyprianou.Ch06.spitzerDivergenceEquivalentToSmallTimeWithFiniteTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:20:00.977817+00:00
-- url     : https://prove2.me/submissions/27d42419-52a7-49d2-b824-9c59150bc3f0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (f : Real → ENNReal)
    (hTail : (∫⁻ t in Set.Ioi (1 : Real), f t ∂volume) < ⊤) :
    (∫⁻ t in Set.Ioi (0 : Real), f t ∂volume) = ⊤ ↔
      (∫⁻ t in Set.Ioc (0 : Real) 1, f t ∂volume) = ⊤ := by
  have hCover :
      Set.Ioi (0 : Real) =
        Set.Ioc (0 : Real) 1 ∪ Set.Ioi 1 := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht
      by_cases h : t ≤ 1
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · linarith
  have hDisjoint :
      Disjoint (Set.Ioc (0 : Real) 1) (Set.Ioi 1) := by
    apply Set.disjoint_left.mpr
    intro t ht1 ht2
    exact (not_lt_of_ge ht1.2) ht2
  rw [hCover, lintegral_union measurableSet_Ioi hDisjoint,
      ENNReal.add_eq_top]
  constructor
  · rintro (hSmall | hLarge)
    · exact hSmall
    · exact False.elim ((ne_of_lt hTail) hLarge)
  · intro hSmall
    exact Or.inl hSmall
