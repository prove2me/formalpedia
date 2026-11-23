-- Prove2me | solution 1 for GlobalTheory.QcSub.isLocalizationAway
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:08.109496+00:00
-- url     : https://prove2.me/submissions/6604295c-9dda-4e28-a606-b313b85d092a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite
open GlobalTheory GlobalTheory.QcSub
variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
variable {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))
namespace GlobalTheory.QcSub
theorem _root_.solution
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W)) :
    letI := (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    IsLocalization.Away ((α.app (op W)).hom f) (F.obj (op (X.basicOpen f))) :=
  Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp hα ⟨W, hW⟩ f
end GlobalTheory.QcSub
