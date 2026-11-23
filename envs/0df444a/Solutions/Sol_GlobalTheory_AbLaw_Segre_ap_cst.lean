-- Prove2me | solution 1 for GlobalTheory.AbLaw.Segre.ap_cst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:06.620855+00:00
-- url     : https://prove2.me/submissions/23b9373d-96dc-4bb0-bbe4-3e0a6ade46a5

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
theorem _root_.solution (p : P ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {W : P.Opens}
    (h : W ≤ p ⁻¹ᵁ U) (r : R) : ap p h (cst f U r) = cst (p ≫ f) W r := by
  refine (ap_rs p h le_top _).trans ?_
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl
end GlobalTheory.AbLaw.Segre
