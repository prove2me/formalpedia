-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.toCech_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:13.432322+00:00
-- url     : https://prove2.me/submissions/8792d35f-d585-43a1-84ea-efc9b98226ab

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
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution {V : X.Opens} (hD : ∀ i, D i ≤ V) (x : SecOnR f M V)
    (s : {s : Finset κ // s.card = 0 + 1}) (h : ⨅ i ∈ s.1, D i ≤ V) :
    toCech M f D hD x s = SecOnR.restrict f M h x := rfl
end GlobalTheory.AbLaw.CechOne
