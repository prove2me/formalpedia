-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_certificate_swap_fixed_complement_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:56:05.565444+00:00
-- url     : https://prove2.me/submissions/a3df7c66-5a4f-4c82-b15e-ce5c6cee7ff0

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_swap_fixed_complement
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_packed_sum_zero

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (hs : c.s = 9)
    (rep : Fin c.s → Fin 24) (hRep : ∀ j, rep j ∈ c.blocks j)
    (j : Fin c.s) {y : Fin 24} (hy : y ∈ c.blocks j)
    (hVal : S (rep j) ≠ S y) :
    (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
      finiteModelEquiv (S (rep k) : G)) = 0 := by
  calc
    (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
      finiteModelEquiv (S (rep k) : G)) =
      ∑ i : Fin 24, finiteModelEquiv (S i : G) :=
        s9_certificate_swap_fixed_complement c hs rep hRep j hy hVal
    _ = 0 := s9_certificate_packed_sum_zero c hs
end InverseZeroSum.Candidate3
