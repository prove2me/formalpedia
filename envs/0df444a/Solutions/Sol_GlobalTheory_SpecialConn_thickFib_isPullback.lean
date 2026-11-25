-- Prove2me | solution 1 for GlobalTheory.SpecialConn.thickFib_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:17:24.230939+00:00
-- url     : https://prove2.me/submissions/14a46215-60b6-4bd2-9511-0be6c97bb5e6

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
    IsPullback (thickι f n) (thickStr f n) f (Spec.map (CommRingCat.ofHom (thickQ O n))) :=
  IsPullback.of_hasPullback _ _
end GlobalTheory.SpecialConn
