-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.readFn_tangentPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:20.113021+00:00
-- url     : https://prove2.me/submissions/9bc31455-8451-4bf6-bb5d-bc18e5f1c5a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
noncomputable section
variable {O : Type u} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
theorem _root_.solution {R : Type u} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R)
    (s : Γ(G.left, ⊤)) :
    readFn ((tangentPt v).left.appTop.hom s) =
      tangentAlg v (G.left.presheaf.germ ⊤ (origin G) trivial s) := by
  show (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom
    ((Spec.map (CommRingCat.ofHom (tangentAlg v).toRingHom) ≫ fromLoc G).appTop.hom s) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, fromLoc, Scheme.fromSpecStalk_appTop]
  simp only [CommRingCat.comp_apply, homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  rw [← CommRingCat.comp_apply (Scheme.Hom.appTop _), Scheme.ΓSpecIso_naturality]
  show (tangentAlg v) ((Scheme.ΓSpecIso (G.left.presheaf.stalk (origin G))).hom
    ((Scheme.ΓSpecIso (G.left.presheaf.stalk (origin G))).inv (G.left.presheaf.germ ⊤ (origin G) trivial s))) = _
  rw [Iso.inv_hom_id_apply]
end GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
