-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_certificate_survivor_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:42:47.529861+00:00
-- url     : https://prove2.me/submissions/c6ce55a9-0159-4d4b-bc2f-112b76ef4fa9

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_representativeSet_update_split
public import Theorems.Thm_InverseZeroSum_Candidate3_complement_insert_swap
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (rep : Fin c.s → Fin 24) (hRep : ∀ j, rep j ∈ c.blocks j)
    (j : Fin c.s) {y : Fin 24}
    (hy : y ∈ c.blocks j) (hxy : rep j ≠ y) :
    (Finset.univ \
        representativeSet (Function.update rep j y)) =
      insert (rep j)
        ((Finset.univ \ representativeSet rep).erase y) ∧
    y ∈ (Finset.univ \ representativeSet rep) ∧
    rep j ∉ (Finset.univ \ representativeSet rep) := by
  classical
  let B : Finset (Fin 24) :=
    ((Finset.univ : Finset (Fin c.s)).erase j).image rep
  have hOldUpdate : Function.update rep j (rep j) = rep := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp
    · simp [Function.update, hkj]
  have hOld : representativeSet rep = insert (rep j) B := by
    have h := representativeSet_update_split rep j (rep j)
    rw [hOldUpdate] at h
    exact h
  have hNew :
      representativeSet (Function.update rep j y) = insert y B := by
    exact representativeSet_update_split rep j y
  have hxB : rep j ∉ B := by
    intro hx
    obtain ⟨k, hk, hEq⟩ := Finset.mem_image.mp hx
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hd := c.pairwise_disjoint j k (Ne.symm hkj)
    exact (Finset.disjoint_left.mp hd) (hRep j)
      (by rw [← hEq]; exact hRep k)
  have hyB : y ∉ B := by
    intro hy'
    obtain ⟨k, hk, hEq⟩ := Finset.mem_image.mp hy'
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hd := c.pairwise_disjoint j k (Ne.symm hkj)
    exact (Finset.disjoint_left.mp hd) hy
      (by rw [← hEq]; exact hRep k)
  have hyOld : y ∈ (Finset.univ \ representativeSet rep) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hOld]
    simpa [Finset.mem_insert, hxy.symm] using hyB
  have hxNotOld : rep j ∉ (Finset.univ \ representativeSet rep) := by
    rw [hOld]
    simp
  refine ⟨?_, hyOld, hxNotOld⟩
  rw [hNew, hOld]
  exact complement_insert_swap B hxB hxy
end InverseZeroSum.Candidate3
