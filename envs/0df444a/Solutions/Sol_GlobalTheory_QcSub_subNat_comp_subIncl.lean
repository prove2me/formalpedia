-- Prove2me | solution 1 for GlobalTheory.QcSub.subNat_comp_subIncl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:45:01.164063+00:00
-- url     : https://prove2.me/submissions/02a6bca6-2740-41dc-807d-e296e382225c

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
theorem _root_.solution :
    subNat F α V T ≫ subIncl F α V T = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α :=
  rfl
end GlobalTheory.QcSub
