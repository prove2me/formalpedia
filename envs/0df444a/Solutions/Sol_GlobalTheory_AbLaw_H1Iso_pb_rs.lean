-- Prove2me | solution 1 for GlobalTheory.AbLaw.H1Iso.pb_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:52:56.244809+00:00
-- url     : https://prove2.me/submissions/590974d5-5000-48e8-8370-27119d389895

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen

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
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory.AbLaw.H1Iso
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLaw.H1Iso
theorem _root_.solution (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (h' : U ≤ U')
    (x : Γ(X, U')) : pb f h (rs X h' x) = pb f (le_pre f h h') x := by
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U W h).hom x = _
  rw [Scheme.Hom.map_appLE]
  rfl
end GlobalTheory.AbLaw.H1Iso
