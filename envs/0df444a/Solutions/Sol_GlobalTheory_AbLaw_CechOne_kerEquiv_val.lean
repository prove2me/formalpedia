-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.kerEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:37:58.015083+00:00
-- url     : https://prove2.me/submissions/cd969475-451c-4e57-b7fc-b4de8fcba28a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen

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
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
variable {κ : Type} [LinearOrder κ] (f : X ⟶ Spec (CommRingCat.of R)) (M) (D : κ → X.Opens)
variable {D}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i)
    (x : SecOnR f M V) : (kerEquiv M f hD hc x).1 = toCech M f D hD x := rfl
end GlobalTheory.AbLaw.CechOne
