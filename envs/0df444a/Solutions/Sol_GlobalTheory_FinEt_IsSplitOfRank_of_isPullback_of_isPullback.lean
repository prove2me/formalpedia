-- Prove2me | solution 1 for GlobalTheory.FinEt.IsSplitOfRank.of_isPullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:13.831821+00:00
-- url     : https://prove2.me/submissions/47b1575e-6320-4d23-82a0-b7b8d7f8bae5

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
theorem _root_.solution {X S X' X'' S' : Scheme.{u}} {a : X' ⟶ X}
    {q : X' ⟶ S'} {a' : X'' ⟶ X} {q' : X'' ⟶ S'} {p : X ⟶ S} {t : S' ⟶ S}
    (H : IsPullback a q p t) (H' : IsPullback a' q' p t) {n : ℕ} (h : IsSplitOfRank q n) :
    IsSplitOfRank q' n :=
  h.of_isPullback (a := (H'.isoIsPullback _ _ H).hom) (t := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩)
end IsSplitOfRank
end GlobalTheory.FinEt
