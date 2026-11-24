-- Prove2me | solution 1 for GlobalTheory.AbLaw.BaseChange.cst_comp_specMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:00.889142+00:00
-- url     : https://prove2.me/submissions/a57225ef-5978-43bf-9e1e-90e834926829

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsProjByBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.BaseChange
namespace GlobalTheory.AbLaw.BaseChange
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {X : Scheme.{0}}
    (f' : X ⟶ Spec (CommRingCat.of R')) (W : X.Opens) (r : R) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) W r = cst f' W (g r) := by
  have h := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).hom r)
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom] at h ⊢
  rw [h]
end GlobalTheory.AbLaw.BaseChange
