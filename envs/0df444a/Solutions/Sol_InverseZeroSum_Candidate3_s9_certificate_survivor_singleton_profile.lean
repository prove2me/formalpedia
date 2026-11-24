-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_certificate_survivor_singleton_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:51:33.543084+00:00
-- url     : https://prove2.me/submissions/f074e3c9-ae44-432d-9820-0b1dc8def8df

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_representativeSet_card_of_pairwise
public import Theorems.Thm_InverseZeroSum_Candidate3_shortFreeOn_card_fifteen_singleton_identity

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (hs : c.s = 9) (rep : Fin c.s → Fin 24)
    (hRep : ∀ j, rep j ∈ c.blocks j) :
    ∃ u : F3T,
      (((Finset.univ \ representativeSet rep).filter
        (fun i => finiteModelEquiv (S i : G) = u)).card = 1) ∧
      (∀ v : F3T,
        ((Finset.univ \ representativeSet rep).filter
          (fun i => finiteModelEquiv (S i : G) = v)).card ≤ 2) ∧
      (∀ v : F3T,
        ((Finset.univ \ representativeSet rep).filter
          (fun i => finiteModelEquiv (S i : G) = v)).card = 1 →
          v = u) ∧
      (∑ i ∈ (Finset.univ \ representativeSet rep),
          finiteModelEquiv (S i : G)) + u = 0 := by
  have hRepCard : (representativeSet rep).card = c.s :=
    representativeSet_card_of_pairwise c.pairwise_disjoint hRep
  have hResidualCard :
      (Finset.univ \ representativeSet rep).card = 15 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), hRepCard, hs]
    decide
  exact shortFreeOn_card_fifteen_singleton_identity S hResidualCard
    (c.every_representative_residual_shortFree rep hRep)
end InverseZeroSum.Candidate3
