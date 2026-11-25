-- Prove2me | solution 1 for GlobalTheory.HodgeTateTest.dlogT_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:16.863833+00:00
-- url     : https://prove2.me/submissions/665e6a75-36dd-47c1-9276-8ccdbfd68301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_GlobalTheory_HodgeTateTest_lie_iff
import Theorems.Thm_GlobalTheory_HodgeTateTest_fst_eq
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_bijective
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
theorem _root_.solution : Function.Bijective (dlogT (O := O)) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (unitOf_bijective (O := O) (R := DualNumber O)).1
    ext
    · rw [fst_eq, fst_eq]
    · exact h
  · intro a
    have hu : IsUnit (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr a : DualNumber O) := by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]; simp
    obtain ⟨w, hw⟩ := (unitOf_bijective (O := O) (R := DualNumber O)).2 hu.unit
    refine ⟨⟨w, (lie_iff w).2 (by rw [hw]; simp)⟩, ?_⟩
    show (unitOf w : DualNumber O).snd = a
    rw [hw]; simp
end GlobalTheory.HodgeTateTest
