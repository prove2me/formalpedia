-- Prove2me | solution 1 for GlobalTheory.FinEt.exists_isSplitOfRank_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:47.256981+00:00
-- url     : https://prove2.me/submissions/39bdb831-6873-4c4c-8de4-26f6cc7a574e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_of_isPullback_of_isPullback
import Theorems.Thm_GlobalTheory_FinEt_exists_isPullback_isSplitOfRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
theorem _root_.solution {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p] [Etale p]
    {n : ℕ} (hn : ∀ s, p.finrank s = n) :
    ∃ (S' : Scheme.{u}) (t : S' ⟶ S), IsFinite t ∧ Etale t ∧ Surjective t ∧
      IsSplitOfRank (pullback.snd p t) n := by
  obtain ⟨S', X', t, a, q, h1, h2, h3, H, hq⟩ := exists_isPullback_isSplitOfRank n p hn
  exact ⟨S', t, h1, h2, h3, hq.of_isPullback_of_isPullback H (IsPullback.of_hasPullback p t)⟩
end GlobalTheory.FinEt
