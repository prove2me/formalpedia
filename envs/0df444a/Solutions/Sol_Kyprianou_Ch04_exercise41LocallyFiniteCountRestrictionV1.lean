-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41LocallyFiniteCountRestrictionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:00:26.111686+00:00
-- url     : https://prove2.me/submissions/e14c0de0-80a8-4363-bd4d-901cbef0f0ae

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    (Z : Set NNReal) (T u : NNReal)
    (hZT : (Z ∩ Iic T).Finite) (hu : u ≤ T) :
    (Z ∩ Iic u).ncard =
      ((hZT.toFinset).filter (fun s => s ≤ u)).card := by
  classical
  have hsub : Z ∩ Iic u ⊆ Z ∩ Iic T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hu⟩
  have huFin : (Z ∩ Iic u).Finite := hZT.subset hsub
  rw [Set.ncard_eq_toFinset_card _ huFin]
  congr 1
  ext s
  simp only [Finset.mem_filter, huFin.mem_toFinset,
    hZT.mem_toFinset, Set.mem_inter_iff, mem_Iic]
  exact ⟨fun hs => ⟨⟨hs.1, hs.2.trans hu⟩, hs.2⟩,
    fun hs => ⟨hs.1.1, hs.2⟩⟩
