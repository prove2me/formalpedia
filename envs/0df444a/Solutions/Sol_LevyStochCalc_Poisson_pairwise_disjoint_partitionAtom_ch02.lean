-- Prove2me | solution 1 for LevyStochCalc.Poisson.pairwise_disjoint_partitionAtom_ch02
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:52:11.766434+00:00
-- url     : https://prove2.me/submissions/24dd66aa-0202-4ad6-972e-f17a0aada380

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory LevyStochCalc.Poisson
set_option autoImplicit false
universe u

theorem solution
    {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ} {C : Fin n → Set 𝓨} :
    Pairwise fun S T => Disjoint (partitionAtom C S) (partitionAtom C T) := by
  intro S T hST
  rw [Set.disjoint_left]
  rintro x ⟨hxS, -⟩ ⟨hxT, -⟩
  exact hST (Finset.ext fun i => (hxS i).symm.trans (hxT i))
