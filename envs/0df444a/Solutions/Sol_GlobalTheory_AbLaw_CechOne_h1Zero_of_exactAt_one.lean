-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.h1Zero_of_exactAt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:31.812628+00:00
-- url     : https://prove2.me/submissions/c9f47f19-4720-4812-a104-f41af2c6ecab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_h1Zero_iff
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_h1ZeroOn_of_exactAt_one

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
theorem _root_.solution (hM : M.IsLB) (hc : ⨆ i, D i = ⊤) (hA : ∀ i, IsAffineOpen (D i))
    (h : (cechLB f M D).ExactAt 1) : FirstCohomologyVanishes M :=
  (h1Zero_iff hM).2 (h1ZeroOn_of_exactAt_one f hM (fun _ => le_top) hc.ge hA h)
end GlobalTheory.AbLaw.CechOne
