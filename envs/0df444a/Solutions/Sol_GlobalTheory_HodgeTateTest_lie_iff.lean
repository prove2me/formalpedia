-- Prove2me | solution 1 for GlobalTheory.HodgeTateTest.lie_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:06:34.109742+00:00
-- url     : https://prove2.me/submissions/4614a5e8-aaa2-4b8d-851a-ffaaee32724c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_P2M_GlobalTheory_HodgeTateTest_unitOf_one__c9598b6cdeb7
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_bijective
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_ptMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateTest
open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
variable {O : Type} [CommRing O]
namespace GlobalTheory.HodgeTateTest
theorem _root_.solution (w : specO O (DualNumber O) ⟶ GmO O) :
    ptMap (TrivSqZeroExt.fstHom O O O) ≫ w = toUnit (specO O O) ≫ η[GmO O] ↔
      (unitOf w : DualNumber O).fst = 1 := by
  have h4 := unitOf_ptMap (TrivSqZeroExt.fstHom O O O) w
  constructor
  · intro h
    rw [h] at h4
    have h1 : unitOf (toUnit (specO O O) ≫ η[GmO O]) = 1 := unitOf_one'
    rw [h1] at h4
    exact h4.symm
  · intro h
    apply (unitOf_bijective (O := O) (R := O)).1
    have h1 : unitOf (toUnit (specO O O) ≫ η[GmO O]) = 1 := unitOf_one'
    rw [h1]
    ext
    rw [h4]
    exact h
end GlobalTheory.HodgeTateTest
