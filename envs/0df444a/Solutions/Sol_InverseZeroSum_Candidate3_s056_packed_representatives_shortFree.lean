-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s056_packed_representatives_shortFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:46:20.340454+00:00
-- url     : https://prove2.me/submissions/deb5c687-309a-4854-a51a-eae915707be6

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_card_two_or_three
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_map_pullSeq
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_s056_shortZero_is_packed_block
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
    {S : PosSeq 24} (hAvoid : AvoidsInnerJointPair S)
    (c : S039PackingCertificate S)
    (h : S8RepresentativeSwapOutput S c)
    (rep : Fin c.s → Fin 24)
    (hRep : ∀ j, rep j ∈ c.blocks j) :
    ShortFree (fun j => S (rep j)) := by
  classical
  have hInj : Function.Injective rep := by
    intro i j hij
    by_contra hne
    have hDisj := c.pairwise_disjoint i j hne
    have hmemj : rep i ∈ c.blocks j := by
      rw [hij]
      exact hRep j
    exact (Finset.disjoint_left.mp hDisj) (hRep i) hmemj
  let e : Fin c.s ↪ Fin 24 := ⟨rep, hInj⟩
  change ∀ I : Finset (Fin c.s), ¬ ShortZero (pullSeq S e) I
  intro I hI
  have hImageShort : ShortZero S (I.map e) :=
    shortZero_map_pullSeq S e hI
  obtain ⟨k, hImageEq⟩ :=
    s056_shortZero_is_packed_block hAvoid c h hImageShort
  have hSub : I ⊆ ({k} : Finset (Fin c.s)) := by
    intro j hj
    by_contra hne
    have hRepInK : rep j ∈ c.blocks k := by
      rw [← hImageEq]
      exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
    have hDisj := c.pairwise_disjoint j k (by simpa using hne)
    exact (Finset.disjoint_left.mp hDisj) (hRep j) hRepInK
  have hSmall : I.card ≤ 1 := by
    calc
      I.card ≤ ({k} : Finset (Fin c.s)).card := Finset.card_le_card hSub
      _ = 1 := by simp
  rcases shortZero_card_two_or_three hI with hTwo | hThree <;> omega
end InverseZeroSum.Candidate3
