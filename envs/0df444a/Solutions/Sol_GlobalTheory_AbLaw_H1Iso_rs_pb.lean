-- Prove2me | solution 1 for GlobalTheory.AbLaw.H1Iso.rs_pb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:52:59.118723+00:00
-- url     : https://prove2.me/submissions/19758a58-9d33-4283-a8ed-a42591ea9067

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
theorem _root_.solution (f : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ W)
    (x : Γ(X, U)) : rs Y h' (pb f h x) = pb f (h'.trans h) x := by
  change (f.appLE U W h ≫ Y.presheaf.map (homOfLE h').op).hom x = _
  rw [Scheme.Hom.appLE_map]
  rfl
end GlobalTheory.AbLaw.H1Iso
