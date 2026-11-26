-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsAdicSum.sub
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:16:50.31417+00:00
-- url     : https://prove2.me/submissions/e0c2ef69-5d6c-4936-9085-741a7bafb0f2

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

theorem solution {a b : ℕ → R} {s t : R} (hs : IsAdicSum I a s) (ht : IsAdicSum I b t) :
    IsAdicSum I (fun n => a n - b n) (s - t) := fun k => by
  obtain ⟨N₁, h₁⟩ := hs k
  obtain ⟨N₂, h₂⟩ := ht k
  refine ⟨N₁ ⊔ N₂, fun M hM => ?_⟩
  have : (s - t) - ∑ n ∈ Finset.range M, (a n - b n) =
      (s - ∑ n ∈ Finset.range M, a n) - (t - ∑ n ∈ Finset.range M, b n) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [this]
  exact sub_mem (h₁ M (le_sup_left.trans hM)) (h₂ M (le_sup_right.trans hM))
