-- Prove2me | solution 1 for InverseZeroSum.Candidate3.tupleSupportT_no_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:43.994902+00:00
-- url     : https://prove2.me/submissions/e60bbcbb-d87a-4302-ad7f-c1462661caeb

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_zero_not_mem_tupleSupportT
public import Theorems.Thm_InverseZeroSum_Candidate3_f3t_self_add_ne_zero
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {n : ℕ} (R : PosSeq n) (hFree : ShortFree R) :
    ∀ x ∈ tupleSupportT R, ∀ y ∈ tupleSupportT R, x + y ≠ 0 := by
  classical
  intro x hx y hy hxy
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy
  have hfi0 : tupleValueT R i ≠ 0 := by
    intro h0
    have hz : (0 : F3T) ∈ tupleSupportT R :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h0⟩
    exact zero_not_mem_tupleSupportT R hz
  have hij : i ≠ j := by
    intro hij
    subst j
    exact (f3t_self_add_ne_zero (tupleValueT R i) hfi0) hxy
  have hGsum : (R i : G) + (R j : G) = 0 := by
    apply finiteModelEquiv.injective
    simpa [tupleValueT] using hxy
  have hIcard : ({i, j} : Finset (Fin n)).card = 2 := by
    simp [hij]
  have hpos : posSum R ({i, j} : Finset (Fin n)) = 0 := by
    simpa [posSum, hij, add_comm] using hGsum
  exact (hFree _) ⟨Finset.card_pos.mp (by omega), by omega, hpos⟩
end InverseZeroSum.Candidate3
