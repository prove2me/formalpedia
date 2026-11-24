-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s056_exists_squarefree_shortFree_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:08:06.592753+00:00
-- url     : https://prove2.me/submissions/31c444a9-38bb-4aca-a1f9-6f33766cdfa0

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_map_pullSeq
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_s056_eight_constant_certificate
public import Theorems.Thm_InverseZeroSum_Candidate3_s056_packed_representatives_shortFree
public import Theorems.Thm_InverseZeroSum_Candidate3_s056_packed_representatives_injective
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution (S : PosSeq 24)
    (hAvoid : AvoidsInnerJointPair S) :
    ∃ U : PosSeq 8, Squarefree U ∧ ShortFree U := by
  classical
  obtain ⟨c, hs, hConst⟩ := s056_eight_constant_certificate S hAvoid
  let rep : Fin c.s → Fin 24 :=
    fun j => Classical.choose (c.block_shortZero j).1
  have hRep : ∀ j, rep j ∈ c.blocks j := by
    intro j
    exact Classical.choose_spec (c.block_shortZero j).1
  let V : PosSeq c.s := fun j => S (rep j)
  have hVFree : ShortFree V :=
    s056_packed_representatives_shortFree hAvoid c hConst rep hRep
  have hVInj : Squarefree V :=
    s056_packed_representatives_injective hAvoid c hs hConst rep hRep
  let e : Fin 8 ↪ Fin c.s :=
    ⟨Fin.cast hs.symm, by
      intro i j hij
      have hh := congrArg (Fin.cast hs) hij
      simpa using hh⟩
  let U : PosSeq 8 := pullSeq V e
  refine ⟨U, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply hVInj
    simpa [U, pullSeq] using hij
  · intro I hI
    apply hVFree (I.map e)
    apply shortZero_map_pullSeq V e
    simpa [U] using hI
end InverseZeroSum.Candidate3
