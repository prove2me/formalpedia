-- Prove2me | solution 1 for GlobalTheory.HodgeTateTest.htSpan_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:01:47.452681+00:00
-- url     : https://prove2.me/submissions/af2c2def-675b-466f-aebd-8e61b87ad457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_GlobalTheory_HodgeTateTest_isAl_taut
import Theorems.Thm_GlobalTheory_HodgeTateTest_dlogT_mem
import Theorems.Thm_GlobalTheory_HodgeTateTest_omega_le_span

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
theorem _root_.solution (p : ℕ) : htSpan (GmO O) p = omega (GmO O) := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun f hf => hf.1
  · exact omega_le_span.trans (Submodule.span_mono (by
      rintro _ rfl
      exact ⟨dlogT_mem, taut p, isAl_taut p⟩))
end GlobalTheory.HodgeTateTest
