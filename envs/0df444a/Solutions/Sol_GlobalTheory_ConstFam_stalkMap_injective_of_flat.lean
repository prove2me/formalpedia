-- Prove2me | solution 1 for GlobalTheory.ConstFam.stalkMap_injective_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:52:31.94861+00:00
-- url     : https://prove2.me/submissions/a14e7d79-8dbe-4d25-8159-63b12f4176e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
namespace GlobalTheory.ConstFam
theorem _root_.solution {Y Z : Scheme.{0}} (r : Z ⟶ Y) [Flat r] (z : Z) :
    Function.Injective (r.stalkMap z).hom := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)
end GlobalTheory.ConstFam
