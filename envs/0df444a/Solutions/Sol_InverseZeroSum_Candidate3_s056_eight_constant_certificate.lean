-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s056_eight_constant_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:05:50.1938+00:00
-- url     : https://prove2.me/submissions/1fdeea2b-2fee-49c9-928e-8efff1bfd7a7

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_s039_signature_s_eq_eight_or_nine
public import Theorems.Thm_InverseZeroSum_Candidate3_s039PackingInput
public import Theorems.Thm_InverseZeroSum_Candidate3_s8RepresentativeSwapInput
public import Theorems.Thm_InverseZeroSum_Candidate3_s9PackingEliminationInput

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution (S : PosSeq 24)
    (hAvoid : AvoidsInnerJointPair S) :
    ∃ c : S039PackingCertificate S,
      c.s = 8 ∧ S8RepresentativeSwapOutput S c := by
  obtain ⟨c⟩ := s039PackingInput S hAvoid
  have hs : c.s = 8 := by
    rcases s039_signature_s_eq_eight_or_nine c.signature with h8 | h9
    · exact h8
    · exact False.elim (s9PackingEliminationInput S c h9)
  exact ⟨c, hs, s8RepresentativeSwapInput S c hs⟩
end InverseZeroSum.Candidate3
