-- Prove2me | solution 2 for InverseZeroSum.Candidate3.zero_not_mem_tupleSupportT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:18.151699+00:00
-- url     : https://prove2.me/submissions/e6ccb00d-cabb-4cdb-b738-0db46c864168

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
theorem _root_.solution {n : ℕ} (R : PosSeq n) :
    (0 : F3T) ∉ tupleSupportT R := by
  intro h0
  obtain ⟨i, _hi, hval⟩ := Finset.mem_image.mp h0
  have hG0 : (R i : G) = 0 := by
    apply finiteModelEquiv.injective
    simpa [tupleValueT] using hval
  exact (R i).property hG0
end InverseZeroSum.Candidate3
