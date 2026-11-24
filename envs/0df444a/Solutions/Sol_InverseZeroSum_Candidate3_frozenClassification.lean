-- Prove2me | solution 1 for InverseZeroSum.Candidate3.frozenClassification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:10:12.342575+00:00
-- url     : https://prove2.me/submissions/effaed6d-d917-4b16-9b4c-8fe77d91f558

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_s056_frozen_necessity
public import Theorems.Thm_InverseZeroSum_Candidate3_s057_canonical_avoids
public import Theorems.Thm_InverseZeroSum_Candidate3_s057_avoids_of_reindexed

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution : FrozenClassification := by
  intro S
  constructor
  · exact s056_frozen_necessity S
  · rintro ⟨U, hInj, hFree, hTriple⟩
    obtain ⟨e, he⟩ := hTriple
    have hReindexed : AvoidsInnerJointPair (fun i => S (e i)) := by
      have hEq : (fun i => S (e i)) = tripleRep U := funext he
      rw [hEq]
      exact s057_canonical_avoids U hInj hFree
    exact s057_avoids_of_reindexed S e hReindexed
end InverseZeroSum.Candidate3
