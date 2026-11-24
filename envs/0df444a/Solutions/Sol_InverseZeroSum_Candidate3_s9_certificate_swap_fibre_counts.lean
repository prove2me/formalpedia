-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_certificate_swap_fibre_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:52.761328+00:00
-- url     : https://prove2.me/submissions/454cc7d6-fddf-4b26-88c7-3f5583f6aeec

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_filter_card_exchange
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_survivor_swap

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (rep : Fin c.s → Fin 24) (hRep : ∀ j, rep j ∈ c.blocks j)
    (j : Fin c.s) {y : Fin 24}
    (hy : y ∈ c.blocks j) (hxy : rep j ≠ y)
    (v : F3T) :
    ((Finset.univ \ representativeSet (Function.update rep j y)).filter
        (fun i => finiteModelEquiv (S i : G) = v)).card +
      (if finiteModelEquiv (S y : G) = v then 1 else 0) =
    ((Finset.univ \ representativeSet rep).filter
        (fun i => finiteModelEquiv (S i : G) = v)).card +
      (if finiteModelEquiv (S (rep j) : G) = v then 1 else 0) := by
  classical
  obtain ⟨hSwap, hyOld, hxOld⟩ :=
    s9_certificate_survivor_swap c rep hRep j hy hxy
  rw [hSwap]
  exact filter_card_exchange
    (Finset.univ \ representativeSet rep)
    (fun i => finiteModelEquiv (S i : G))
    hxOld hyOld v
end InverseZeroSum.Candidate3
