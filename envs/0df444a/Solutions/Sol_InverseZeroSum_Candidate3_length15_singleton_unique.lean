-- Prove2me | solution 1 for InverseZeroSum.Candidate3.length15_singleton_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:08.632065+00:00
-- url     : https://prove2.me/submissions/f4645b44-df3a-4469-abd5-8854aa34cda9

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_eq_two_off_singleton_length15

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    (R : PosSeq 15) (hFree : ShortFree R)
    {u : F3T} (hu : u ∈ tupleSupportT R)
    (huOne :
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = u)).card = 1)
    {v : F3T} (hv : v ∈ tupleSupportT R)
    (hvOne :
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = v)).card = 1) :
    v = u := by
  by_contra hne
  have hvErase : v ∈ (tupleSupportT R).erase u :=
    Finset.mem_erase.mpr ⟨hne, hv⟩
  have hvTwo :=
    tupleFiberT_card_eq_two_off_singleton_length15
      R hFree hu huOne v hvErase
  omega
end InverseZeroSum.Candidate3
