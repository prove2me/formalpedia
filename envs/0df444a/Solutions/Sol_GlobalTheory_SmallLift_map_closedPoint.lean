-- Prove2me | solution 1 for GlobalTheory.SmallLift.map_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:18.676791+00:00
-- url     : https://prove2.me/submissions/17e61ed5-d1f4-453b-9cd3-3bb801c6ba04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLifting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.SmallLift
namespace GlobalTheory.SmallLift
theorem _root_.solution {X : Scheme.{0}} {x : X} {R : CommRingCat.{0}} [IsLocalRing R]
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (closedPoint R) = x := by
  refine (Scheme.Hom.comp_apply (Spec.map φ) (X.fromSpecStalk x) (closedPoint R)).trans ?_
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := φ))).trans
    Scheme.fromSpecStalk_closedPoint
end GlobalTheory.SmallLift
