-- Prove2me | solution 1 for GlobalTheory.HodgeTateTest.htChar_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:39.923498+00:00
-- url     : https://prove2.me/submissions/efac4142-6af2-42d7-87ec-f48be1753474

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateTest
open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
variable {O : Type} [CommRing O]
namespace GlobalTheory.HodgeTateTest
theorem _root_.solution (p : ℕ) (hp : IsUnit (p : O)) {C : Type} [Field C]
    (v : Valuation C NNReal) [Algebra O C] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] :
    HTChar p v G := by
  intro c _ f hf
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hf, ⟨fun _ => 1, ?_, ?_⟩, ?_⟩)
  · intro n T x y z _
    simp only [MonObj.comp_one, _root_.mul_one]
  · intro n T x y _
    simp only [MonObj.comp_one]
  · intro n R _ _ hR x w _
    have hu : IsUnit ((p : R) ^ n) := by
      have := hp.map (algebraMap O R)
      rw [map_natCast] at this
      exact this.pow n
    rw [hR, isUnit_zero_iff] at hu
    haveI : Subsingleton R := subsingleton_of_zero_eq_one hu
    ext <;> exact Subsingleton.elim _ _
end GlobalTheory.HodgeTateTest
