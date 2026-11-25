-- Prove2me | solution 1 for GlobalTheory.SpecialConn.thickTr_str
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:17:29.10156+00:00
-- url     : https://prove2.me/submissions/b725c120-34f4-458c-a8e9-5bf8309c2f45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThickFibIsPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.SpecialConn
variable {O : Type} [CommRing O] [IsLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of O))
namespace GlobalTheory.SpecialConn
theorem _root_.solution (n : ℕ) :
    thickTr f n ≫ thickStr f (n + 1) = thickStr f n ≫ Spec.map (CommRingCat.ofHom (thickR O n)) :=
  pullback.lift_snd _ _ _
end GlobalTheory.SpecialConn
