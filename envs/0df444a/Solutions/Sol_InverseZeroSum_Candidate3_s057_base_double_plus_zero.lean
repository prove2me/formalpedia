-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s057_base_double_plus_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:30.294268+00:00
-- url     : https://prove2.me/submissions/f41bf51b-41be-4855-a740-863907be6979

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
    (U : PosSeq 8) (hInj : Squarefree U)
    (a b : Fin 8)
    (hZero : (U a : G) + (U a : G) + (U b : G) = 0) :
    a = b := by
  have hTuple :
      finiteModelEquiv (U a : G) +
        finiteModelEquiv (U a : G) +
          finiteModelEquiv (U b : G) = 0 := by
    simpa using congrArg finiteModelEquiv hZero
  have hIdentity :
      ∀ x y : F3T, x + x + y = 0 → x = y := by decide
  apply hInj
  apply Subtype.ext
  apply finiteModelEquiv.injective
  exact hIdentity _ _ hTuple
end InverseZeroSum.Candidate3
