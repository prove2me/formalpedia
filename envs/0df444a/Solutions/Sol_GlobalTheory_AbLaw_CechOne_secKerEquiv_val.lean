-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.secKerEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:25.527605+00:00
-- url     : https://prove2.me/submissions/266533ad-3349-44ab-baa0-0051ef10852f

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
theorem _root_.solution (hc : ⨆ i, D i = ⊤) (σ : LB.Sec M) (s : {s : Finset κ // s.card = 0 + 1}) :
    (secKerEquiv M f hc σ).1 s = SecOnR.of f M _ (GlobalTheory.LB.ofSec σ (⨅ i ∈ s.1, D i)) :=
  restrict_ofSec σ le_top
end GlobalTheory.AbLaw.CechOne
