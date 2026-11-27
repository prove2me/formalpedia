-- Prove2me | solution 1 for GlobalTheory.UniversalConstants.bijective_appTop_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:36.514545+00:00
-- url     : https://prove2.me/submissions/ac55e0bd-ba95-44dd-aa40-3a2f9c0255d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BijectiveAppTopBaseChange
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_baseChange_of_field


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
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.UniversalConstants
namespace GlobalTheory.UniversalConstants
theorem _root_.solution : ∀ (R : Type) [Field R] (X : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X), IsProper X.hom → GeometricallyIntegral X.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) := by
  intro R _ X _ hp hg R' _ g X' π f' H
  have := GlobalTheory.ProperFunctions.isIso_appTop_baseChange_of_field H
  exact ConcreteCategory.bijective_of_isIso f'.appTop
end GlobalTheory.UniversalConstants
