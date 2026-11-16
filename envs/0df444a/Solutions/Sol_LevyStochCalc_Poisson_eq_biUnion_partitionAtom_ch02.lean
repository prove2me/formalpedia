-- Prove2me | solution 1 for LevyStochCalc.Poisson.eq_biUnion_partitionAtom_ch02
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:52:26.633689+00:00
-- url     : https://prove2.me/submissions/2f19d93a-3506-4398-a70c-71b3dfc42333

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory LevyStochCalc.Poisson
set_option autoImplicit false
universe u

theorem solution
    {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ} {C : Fin n → Set 𝓨} (i : Fin n) :
    C i = ⋃ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), partitionAtom C S := by
  classical
  ext x
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
  constructor
  · intro hx
    exact ⟨Finset.univ.filter (fun j => x ∈ C j), by simpa using hx,
      fun j => by simp, Set.mem_iUnion.mpr ⟨i, hx⟩⟩
  · rintro ⟨S, hiS, hxS, -⟩
    exact (hxS i).mpr hiS
