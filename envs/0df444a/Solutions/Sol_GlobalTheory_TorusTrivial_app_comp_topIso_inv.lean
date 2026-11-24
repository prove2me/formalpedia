-- Prove2me | solution 1 for GlobalTheory.TorusTrivial.app_comp_topIso_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:04.684833+00:00
-- url     : https://prove2.me/submissions/3b202b13-ca7f-47bf-be55-7f57e60aa4f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusTrivial
namespace GlobalTheory.TorusTrivial
theorem _root_.solution {Y Z : Scheme.{0}} (f : Y ⟶ Z) (V : Z.Opens) :
    f.app V ≫ (f ⁻¹ᵁ V).topIso.inv = V.topIso.inv ≫ (f ∣_ V).appTop := by
  rw [Scheme.Hom.appTop, morphismRestrict_app', Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
    Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.map_appLE _ _ _).symm
end GlobalTheory.TorusTrivial
