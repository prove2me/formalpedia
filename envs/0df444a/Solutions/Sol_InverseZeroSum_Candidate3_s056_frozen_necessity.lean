-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s056_frozen_necessity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:08:05.978509+00:00
-- url     : https://prove2.me/submissions/289769d5-b0ae-497b-9afa-67634a88f1eb

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
public import Theorems.Thm_InverseZeroSum_Candidate3_s056_constant_blocks_isTriplePower
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
    ∃ U : PosSeq 8,
      Squarefree U ∧ ShortFree U ∧ IsTriplePower S U := by
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
  have hUInj : Squarefree U := by
    intro i j hij
    apply e.injective
    apply hVInj
    simpa [U, pullSeq] using hij
  have hUFree : ShortFree U := by
    intro I hI
    apply hVFree (I.map e)
    apply shortZero_map_pullSeq V e
    simpa [U] using hI
  have hTriple :
      IsTriplePower S (fun i : Fin 8 =>
        S (rep (Fin.cast hs.symm i))) :=
    s056_constant_blocks_isTriplePower c hs hConst rep hRep
  refine ⟨U, hUInj, hUFree, ?_⟩
  change IsTriplePower S (fun i : Fin 8 => S (rep (Fin.cast hs.symm i)))
  exact hTriple
end InverseZeroSum.Candidate3
