-- Prove2me | solution 1 for GlobalTheory.AbLaw.H1Iso.pb_of_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:06.338426+00:00
-- url     : https://prove2.me/submissions/6d36e4d0-5c1f-439c-bb11-144ecdf3a38d

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
theorem _root_.solution (g : X ⟶ X) (hg : g = 𝟙 X) {U W : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (h' : W ≤ U)
    (x : Γ(X, U)) : pb g h x = rs X h' x := by
  subst hg
  change (𝟙 _ ≫ X.presheaf.map (homOfLE h').op).hom x = _
  rw [Category.id_comp]
end GlobalTheory.AbLaw.H1Iso
