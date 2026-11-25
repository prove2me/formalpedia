-- Prove2me | solution 1 for GlobalTheory.T.exists_specializes_lift_pullback_snd_fromSpecStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:16:22.340586+00:00
-- url     : https://prove2.me/submissions/ce72157b-507f-4f33-bf39-b36360fc5a21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecializesLiftClosedFibreStalkBaseChange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecializesLiftClosedFibreStalkBaseChangeStatement
import Theorems.Thm_GlobalTheory_specializes_lift_closedFibre_stalkBaseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by
  first | exact @GlobalTheory.specializes_lift_closedFibre_stalkBaseChange | exact GlobalTheory.specializes_lift_closedFibre_stalkBaseChange | (intros; apply GlobalTheory.specializes_lift_closedFibre_stalkBaseChange <;> assumption)
end _root_.GlobalTheory.T
