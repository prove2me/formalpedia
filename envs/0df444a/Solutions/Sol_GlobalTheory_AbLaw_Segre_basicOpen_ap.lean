-- Prove2me | solution 1 for GlobalTheory.AbLaw.Segre.basicOpen_ap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:01.224955+00:00
-- url     : https://prove2.me/submissions/9659d0fc-5289-4379-a1e8-841040fb96f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback

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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.AbLaw.Segre
theorem _root_.solution (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (x : Γ(X, U)) :
    P.basicOpen (ap p h x) = W ⊓ p ⁻¹ᵁ X.basicOpen x :=
  Scheme.basicOpen_appLE p W U h x
end GlobalTheory.AbLaw.Segre
