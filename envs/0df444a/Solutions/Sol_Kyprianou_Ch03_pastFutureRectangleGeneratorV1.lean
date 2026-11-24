-- Prove2me | solution 1 for Kyprianou.Ch03.pastFutureRectangleGeneratorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:51:46.936781+00:00
-- url     : https://prove2.me/submissions/88609057-f1af-44e9-99d2-605d9dd81daf

import Mathlib.MeasureTheory.PiSystem
open MeasureTheory
set_option autoImplicit false

theorem solution {Omega : Type} (m h : MeasurableSpace Omega) :
    m ⊔ h = MeasurableSpace.generateFrom
      {S : Set Omega | ∃ B C : Set Omega, MeasurableSet[m] B ∧ MeasurableSet[h] C ∧ S = B ∩ C}
    ∧ IsPiSystem
      {S : Set Omega | ∃ B C : Set Omega, MeasurableSet[m] B ∧ MeasurableSet[h] C ∧ S = B ∩ C} := by
  have hm : m ≤ m ⊔ h := le_sup_left
  have hh : h ≤ m ⊔ h := le_sup_right
  constructor
  · apply le_antisymm
    · apply sup_le
      · intro B hB
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨B, Set.univ, hB, MeasurableSet.univ, (Set.inter_univ B).symm⟩
      · intro C hC
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨Set.univ, C, MeasurableSet.univ, hC, (Set.univ_inter C).symm⟩
    · apply MeasurableSpace.generateFrom_le
      rintro S ⟨B, C, hB, hC, rfl⟩
      exact (hm _ hB).inter (hh _ hC)
  · rintro S ⟨B, C, hB, hC, rfl⟩ T ⟨D, E, hD, hE, rfl⟩ _
    refine ⟨B ∩ D, C ∩ E, hB.inter hD, hC.inter hE, ?_⟩
    ext x
    simp only [Set.mem_inter_iff]
    tauto
