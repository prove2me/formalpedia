-- Prove2me | solution 1 for MultiPartyError1146.Adaptive.optimal_error_resilience
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:19:07.381116+00:00
-- url     : https://prove2.me/submissions/919b2975-2366-4347-91ce-5404feb5aa86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MultiPartyError1146_Adaptive_achievability
import Theorems.Thm_MultiPartyError1146_Adaptive_erasure_converse

set_option autoImplicit false

open MultiPartyError1146.Adaptive

theorem solution : Achievability ∧ Converse := by
  refine ⟨achievability, ⟨6, by norm_num, ?_⟩⟩
  intro n m T hn hm hT P δ hδ
  exact erasure_converse n m T hn hm hT P δ hδ
