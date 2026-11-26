-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsAdicSum.neg
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:18:43.210724+00:00
-- url     : https://prove2.me/submissions/d394974d-68a9-445b-8363-08d10c4d513e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {I}

theorem solution {a : ℕ → R} {s : R} (hs : IsAdicSum I a s) :
    IsAdicSum I (fun n => -a n) (-s) := fun k => by
  obtain ⟨N, hN⟩ := hs k
  refine ⟨N, fun M hM => ?_⟩
  have : -s - ∑ n ∈ Finset.range M, -a n = - (s - ∑ n ∈ Finset.range M, a n) := by
    rw [Finset.sum_neg_distrib]
    ring
  rw [this]
  exact neg_mem (hN M hM)
