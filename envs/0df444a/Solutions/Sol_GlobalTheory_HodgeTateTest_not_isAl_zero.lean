-- Prove2me | solution 1 for GlobalTheory.HodgeTateTest.not_isAl_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:45.267063+00:00
-- url     : https://prove2.me/submissions/59a74af6-9960-46e1-b194-cf95d3da6a8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_GlobalTheory_HodgeTateTest_isAl_taut
import Theorems.Thm_GlobalTheory_HodgeTateTest_dlogT_bijective
import Theorems.Thm_GlobalTheory_HodgeTateImage_isAl_iff
import Theorems.Thm_GlobalTheory_HodgeTateImage_pow_quot


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
theorem _root_.solution (p : ℕ) (hp : ¬IsUnit (p : O)) : ¬IsAl (taut (O := O) p) 0 := by
  intro h
  obtain ⟨e, he⟩ := (dlogT_bijective (O := O)).2 1
  have h1 := (isAl_iff _ _).1 h e 1 _ (pow_quot (O := O) 1)
  have h2 := (isAl_iff _ _).1 (isAl_taut (O := O) p) e 1 _ (pow_quot (O := O) 1)
  rw [← h1, he, Pi.zero_apply, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, sub_zero,
    pow_one, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top] at h2
  exact hp h2
end GlobalTheory.HodgeTateTest
