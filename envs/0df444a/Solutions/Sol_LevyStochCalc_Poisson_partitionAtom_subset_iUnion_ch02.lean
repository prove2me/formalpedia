-- Prove2me | solution 1 for LevyStochCalc.Poisson.partitionAtom_subset_iUnion_ch02
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:52:19.675204+00:00
-- url     : https://prove2.me/submissions/024f6426-17a2-4af9-a910-92600a3fbae1

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory LevyStochCalc.Poisson
set_option autoImplicit false
universe u

theorem solution
    {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ} {C : Fin n → Set 𝓨} (S : Finset (Fin n)) :
    partitionAtom C S ⊆ ⋃ i, C i := by
  exact Set.inter_subset_right
