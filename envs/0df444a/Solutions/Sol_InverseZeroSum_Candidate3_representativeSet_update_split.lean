-- Prove2me | solution 1 for InverseZeroSum.Candidate3.representativeSet_update_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:01.659945+00:00
-- url     : https://prove2.me/submissions/56e72360-97b3-4995-8acc-ee45aaf35402

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution {s : ℕ}
    (base : Fin s → Fin 24) (j : Fin s) (z : Fin 24) :
    representativeSet (Function.update base j z) =
      insert z (((Finset.univ : Finset (Fin s)).erase j).image base) := by
  classical
  unfold representativeSet
  ext x
  constructor
  · intro hx
    obtain ⟨k, _hk, hval⟩ := Finset.mem_image.mp hx
    by_cases hkj : k = j
    · apply Finset.mem_insert.mpr
      left
      subst k
      simpa [Function.update] using hval.symm
    · apply Finset.mem_insert.mpr
      right
      refine Finset.mem_image.mpr
        ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩, ?_⟩
      simpa [Function.update, hkj] using hval
  · intro hx
    rcases Finset.mem_insert.mp hx with hval | hother
    · refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
      simpa using hval.symm
    · obtain ⟨k, hk, hval⟩ := Finset.mem_image.mp hother
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
      simpa [Function.update, hkj] using hval
end InverseZeroSum.Candidate3
