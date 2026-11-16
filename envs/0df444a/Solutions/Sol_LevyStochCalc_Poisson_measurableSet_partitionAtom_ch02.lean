-- Prove2me | solution 1 for LevyStochCalc.Poisson.measurableSet_partitionAtom_ch02
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:52:03.54024+00:00
-- url     : https://prove2.me/submissions/e6e9095b-9476-4db9-8d95-dc378555ff5c

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory LevyStochCalc.Poisson
set_option autoImplicit false
universe u

theorem solution
    {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ} {C : Fin n → Set 𝓨} (hC : ∀ i, MeasurableSet (C i)) (S : Finset (Fin n)) :
    MeasurableSet (partitionAtom C S) := by
  classical
  refine MeasurableSet.inter ?_ (MeasurableSet.iUnion hC)
  have h : {x | ∀ i, x ∈ C i ↔ i ∈ S} = ⋂ i, (if i ∈ S then C i else (C i)ᶜ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' fun i => ?_
    by_cases h : i ∈ S <;> simp [h]
  rw [h]
  exact MeasurableSet.iInter fun i => by split_ifs; exacts [hC i, (hC i).compl]
