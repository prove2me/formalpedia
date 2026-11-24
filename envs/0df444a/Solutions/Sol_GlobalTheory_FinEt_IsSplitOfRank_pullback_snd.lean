-- Prove2me | solution 1 for GlobalTheory.FinEt.IsSplitOfRank.pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:44.396374+00:00
-- url     : https://prove2.me/submissions/5804135a-33b2-4bdf-a67e-431a4f300377

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_of_isPullback

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
namespace IsSplitOfRank
theorem _root_.solution {X S S' : Scheme.{u}} {p : X ⟶ S} {n : ℕ}
    (h : IsSplitOfRank p n) (t : S' ⟶ S) : IsSplitOfRank (pullback.snd p t) n :=
  h.of_isPullback (IsPullback.of_hasPullback p t)
end IsSplitOfRank
end GlobalTheory.FinEt
