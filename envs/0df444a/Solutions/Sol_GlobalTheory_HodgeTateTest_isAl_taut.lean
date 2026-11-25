-- Prove2me | solution 1 for GlobalTheory.HodgeTateTest.isAl_taut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:03.072675+00:00
-- url     : https://prove2.me/submissions/75107746-56d4-4d80-982d-c237c0c40541

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_GlobalTheory_HodgeTateTest_fst_eq
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_ptMap
import Theorems.Thm_GlobalTheory_HodgeTateImage_dualBC_fst
import Theorems.Thm_GlobalTheory_HodgeTateImage_dualBC_snd
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
theorem _root_.solution (p : ℕ) : IsAl (taut (O := O) p) dlogT := by
  intro n R _ _ _ x w hw
  have hw' : w ≫ (taut (O := O) p).χ n = _ := hw
  rw [hw', unitOf_ptMap]
  ext
  · simp [dualBC_fst, fst_eq]
  · rw [dualBC_snd, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl
end GlobalTheory.HodgeTateTest
