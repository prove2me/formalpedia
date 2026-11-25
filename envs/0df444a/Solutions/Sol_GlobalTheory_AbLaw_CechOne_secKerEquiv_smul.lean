-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.secKerEquiv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:20.893452+00:00
-- url     : https://prove2.me/submissions/ce769267-7fa0-45f9-8da9-a41aaa346622

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
theorem _root_.solution (hc : ⨆ i, D i = ⊤) (r : R) (σ : LB.Sec M) :
    secKerEquiv M f hc (cst f ⊤ r • σ) = r • secKerEquiv M f hc σ :=
  (congrArg (kerEquiv M f (fun _ => le_top) hc.ge)
    ((SecOnR.topEquiv f M).symm.map_smul (cst f ⊤ r) σ)).trans
    ((kerEquiv M f (fun _ => le_top) hc.ge).map_smul r _)
end GlobalTheory.AbLaw.CechOne
