-- Prove2me | solution 1 for GlobalTheory.HodgeTateTest.htChar_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:34.426393+00:00
-- url     : https://prove2.me/submissions/7f5428f7-c772-4ee4-b16a-a0c3279433fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_GlobalTheory_HodgeTateTest_dlogT_mem
import Theorems.Thm_GlobalTheory_HodgeTateTest_dlogT_bijective
import Theorems.Thm_GlobalTheory_HodgeTateTest_htSpan_gm

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
theorem _root_.solution (p : ℕ) {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]
    [Nontrivial O] : HTChar p v (GmO O) ∧ omega (GmO O) ≠ ⊥ := by
  refine ⟨fun c _ f hf => ?_, fun h => ?_⟩
  · rw [htSpan_gm]; exact Submodule.smul_mem _ _ hf
  · have h0 : dlogT (O := O) = 0 := by
      have := dlogT_mem (O := O); rwa [h, Submodule.mem_bot] at this
    obtain ⟨e, he⟩ := (dlogT_bijective (O := O)).2 1
    rw [h0] at he
    exact zero_ne_one he
end GlobalTheory.HodgeTateTest
