-- Prove2me | solution 1 for GlobalTheory.eq_comp_section_of_surjective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:42.809919+00:00
-- url     : https://prove2.me/submissions/33c695a7-a8c7-4f36-b1be-9fac90e58286

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop

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
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {X T Y : Scheme.{0}} [IsAffine Y] (p : X ⟶ T)
    (ε : T ⟶ X) (g : X ⟶ Y) (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) :
    g = p ≫ ε ≫ g := by
  refine ext_of_isAffine ?_
  ext a
  obtain ⟨b, hb⟩ := hs (g.appTop.hom a)
  have hεp : ε.appTop.hom (p.appTop.hom b) = b := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h]
    simp
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [← hb, hεp]
end _root_.GlobalTheory
end GlobalTheory
