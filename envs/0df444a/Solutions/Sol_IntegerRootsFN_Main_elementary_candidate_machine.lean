-- Prove2me | solution 1 for IntegerRootsFN.Main.elementary_candidate_machine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:43:51.458378+00:00
-- url     : https://prove2.me/submissions/660e0b66-5250-4ca9-81ae-ad6c42c76a63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline
import Theorems.Thm_IntegerRootsFN_Main_elementary_candidate_data
import Theorems.Thm_IntegerRootsFN_Main_elementary_candidate_runtime

set_option autoImplicit false

open IntegerRootsFN.Main

theorem solution
    (hsearch : ElementarySearchContract) :
    CandidateAlgorithm (fun n b => (n : ℝ) * b + (min n b : ℕ) ^ 3 * (b : ℝ) ^ 2) := by
  obtain ⟨Kcard, Ksize, hdata⟩ := elementary_candidate_data hsearch
  obtain ⟨M, C, hC, k, l, hrun⟩ := elementary_candidate_runtime hsearch
  refine ⟨M, C, k, l, Kcard, Ksize, hC, ?_⟩
  intro n b f hf
  obtain ⟨hcover, hlength, hsize⟩ := hdata n b f hf
  exact ⟨[-1, 0, 1] ++ searchCandidates f n b,
    hcover, hlength, hsize, hrun n b f hf⟩
