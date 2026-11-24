-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s056_packed_representatives_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:28.91563+00:00
-- url     : https://prove2.me/submissions/ab1823c1-6b1d-4b24-b2d1-559c72c242b5

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_disjoint_of_ne
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_sum_erase_insert_exchange
public import Theorems.Thm_InverseZeroSum_Candidate3_s056_eight_constant_block_card
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
    (c : S039PackingCertificate S) (hs : c.s = 8)
    (h : S8RepresentativeSwapOutput S c)
    (rep : Fin c.s → Fin 24)
    (hRep : ∀ j, rep j ∈ c.blocks j) :
    Function.Injective (fun j => S (rep j)) := by
  classical
  intro j k hEq
  by_contra hNe
  have hNotK : rep k ∉ c.blocks j := by
    intro hk
    exact (Finset.disjoint_left.mp
      (c.pairwise_disjoint k j (Ne.symm hNe))) (hRep k) hk
  have hCard := s056_eight_constant_block_card c hs h j
  let I : Finset (Fin 24) :=
    insert (rep k) ((c.blocks j).erase (rep j))
  have hEraseCard : ((c.blocks j).erase (rep j)).card = 2 := by
    rw [Finset.card_erase_of_mem (hRep j), hCard]
  have hNotErase : rep k ∉ (c.blocks j).erase (rep j) := by
    intro hk
    exact hNotK (Finset.mem_of_mem_erase hk)
  have hICard : I.card = 3 := by
    simp [I, hNotErase, hEraseCard]
  have hBalance :
      posSum S I + (S (rep j) : G) =
        posSum S (c.blocks j) + (S (rep k) : G) := by
    simpa [I, posSum] using
      (sum_erase_insert_exchange (c.blocks j)
        (fun z => (S z : G)) hNotK (hRep j))
  have hEqG : (S (rep j) : G) = (S (rep k) : G) :=
    congrArg Subtype.val hEq
  rw [← hEqG] at hBalance
  have hISum : posSum S I = posSum S (c.blocks j) :=
    add_right_cancel hBalance
  have hIShort : ShortZero S I := by
    refine ⟨Finset.card_pos.mp (by omega), by omega, ?_⟩
    rw [hISum]
    exact (c.block_shortZero j).2.2
  have hINe : I ≠ c.blocks j := by
    intro heq
    apply hNotK
    rw [← heq]
    exact Finset.mem_insert_self _ _
  have hDisj :=
    shortZero_disjoint_of_ne hAvoid hIShort (c.block_shortZero j) hINe
  have hEraseNonempty : ((c.blocks j).erase (rep j)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hEraseNonempty
  exact (Finset.disjoint_left.mp hDisj)
    (Finset.mem_insert_of_mem hz) (Finset.mem_of_mem_erase hz)
end InverseZeroSum.Candidate3
