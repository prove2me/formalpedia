-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s057_base_pair_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:42:26.464075+00:00
-- url     : https://prove2.me/submissions/a4009c29-4dee-4a8e-86b4-653ca2e7c2bf

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_f3t_self_add_ne_zero
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution (U : PosSeq 8)
    (hFree : ShortFree U) (a b : Fin 8) :
    (U a : G) + (U b : G) ≠ 0 := by
  classical
  by_cases hab : a = b
  · subst b
    intro hZero
    have hNonzero : finiteModelEquiv (U a : G) ≠ 0 := by
      intro h
      apply (U a).property
      apply finiteModelEquiv.injective
      simpa using h
    apply f3t_self_add_ne_zero _ hNonzero
    simpa using congrArg finiteModelEquiv hZero
  · intro hZero
    have hShort : ShortZero U ({a, b} : Finset (Fin 8)) := by
      refine ⟨by simp, by simp [hab], ?_⟩
      simpa [posSum, hab, add_comm] using hZero
    exact hFree _ hShort
end InverseZeroSum.Candidate3
