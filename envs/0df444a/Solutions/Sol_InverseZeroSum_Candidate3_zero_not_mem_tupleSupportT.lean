-- Prove2me | solution 1 for InverseZeroSum.Candidate3.zero_not_mem_tupleSupportT
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:27:03.089117+00:00
-- url     : https://prove2.me/submissions/82370509-a89a-448c-b0da-ccf1e4cb3165

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3


theorem solution {n : ℕ} (R : PosSeq n) :
    (0 : F3T) ∉ tupleSupportT R := by
  intro hz; obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
  exact (R i).property (finiteModelEquiv.injective (hi.trans (map_zero finiteModelEquiv).symm))
