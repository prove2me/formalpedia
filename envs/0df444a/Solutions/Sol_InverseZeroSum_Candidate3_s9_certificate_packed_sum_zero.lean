-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_certificate_packed_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:55.893792+00:00
-- url     : https://prove2.me/submissions/97f20f02-6348-416a-ae0f-65bae69d7c85

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
theorem _root_.solution
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (hs : c.s = 9) :
    (∑ i : Fin 24, finiteModelEquiv (S i : G)) = 0 := by
  classical
  have hr : c.r = 0 := by
    rcases c.signature with h | h | h | h <;> omega
  have hEmpty :
      (Finset.univ \ blockUnion c.blocks) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [hr] using c.remainder_card
  have hAll : blockUnion c.blocks = Finset.univ := by
    ext i
    constructor
    · intro _
      exact Finset.mem_univ i
    · intro _
      by_contra hnot
      have hi : i ∈ (Finset.univ \ blockUnion c.blocks) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hnot⟩
      simpa [hEmpty] using hi
  have hPair :
      ((Finset.univ : Finset (Fin c.s)) : Set (Fin c.s)).PairwiseDisjoint
        c.blocks := by
    intro i _hi j _hj hij
    exact c.pairwise_disjoint i j hij
  let f : Fin 24 → F3T := fun i => finiteModelEquiv (S i : G)
  have hBlockSum :
      (∑ i ∈ blockUnion c.blocks, f i) =
      ∑ j : Fin c.s, ∑ i ∈ c.blocks j, f i := by
    simpa [blockUnion] using (Finset.sum_biUnion hPair (f := f))
  have hBlocksZero :
      ∀ j : Fin c.s, (∑ i ∈ c.blocks j, f i) = 0 := by
    intro j
    have hz := congrArg finiteModelEquiv (c.block_shortZero j).2.2
    simpa [posSum, f] using hz
  calc
    (∑ i : Fin 24, finiteModelEquiv (S i : G)) =
        (∑ i ∈ blockUnion c.blocks, f i) := by simp [hAll, f]
    _ = ∑ j : Fin c.s, ∑ i ∈ c.blocks j, f i := hBlockSum
    _ = 0 := by simp [hBlocksZero]
end InverseZeroSum.Candidate3
