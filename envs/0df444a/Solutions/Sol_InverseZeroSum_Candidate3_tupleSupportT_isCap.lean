-- Prove2me | solution 1 for InverseZeroSum.Candidate3.tupleSupportT_isCap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:43.453646+00:00
-- url     : https://prove2.me/submissions/bc6a0a3d-37e3-43d8-881f-e461e1582574

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
namespace InverseZeroSum.Candidate3
theorem _root_.solution {n : ℕ} (R : PosSeq n) (hFree : ShortFree R) :
    IsCapT (tupleSupportT R) := by
  classical
  intro x hx y hy z hz hxy hxz hyz hxyz
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hz
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hxy rfl
  have hik : i ≠ k := by
    intro hik
    subst k
    exact hxz rfl
  have hjk : j ≠ k := by
    intro hjk
    subst k
    exact hyz rfl
  have hGsum : (R i : G) + (R j : G) + (R k : G) = 0 := by
    apply finiteModelEquiv.injective
    simpa [tupleValueT] using hxyz
  have hIcard : ({i, j, k} : Finset (Fin n)).card = 3 := by
    simp [hij, hik, hjk]
  have hpos : posSum R ({i, j, k} : Finset (Fin n)) = 0 := by
    simpa [posSum, hij, hik, hjk, add_assoc] using hGsum
  exact (hFree _) ⟨Finset.card_pos.mp (by omega), by omega, hpos⟩
end InverseZeroSum.Candidate3
