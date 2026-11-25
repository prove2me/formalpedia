-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.h1ZeroOn_of_exactAt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:49:08.799886+00:00
-- url     : https://prove2.me/submissions/30bd8085-98b7-4e9c-88f3-20f2894b2a29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_cechHOneVanishesOnOpen_of_cover
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_cechHOneVanishesOnOpen_of_isAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_isCoboundary_of_exactAt

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
variable {M}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution (hM : M.IsLB) {V : X.Opens} (hD : ∀ i, D i ≤ V)
    (hc : V ≤ ⨆ i, D i) (hA : ∀ i, IsAffineOpen (D i)) (h : (cechLB f M D).ExactAt 1) :
    CechHOneVanishesOnOpen M V :=
  cechHOneVanishesOnOpen_of_cover hD hc (fun i => cechHOneVanishesOnOpen_of_isAffineOpen hM (hA i)) (isCoboundary_of_exactAt h)
end GlobalTheory.AbLaw.CechOne
