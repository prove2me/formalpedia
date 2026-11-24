-- Prove2me | solution 1 for GlobalTheory.Hk.LFamPos.summable_lamChi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:47:48.548177+00:00
-- url     : https://prove2.me/submissions/0cb35a51-15ea-4227-850c-1f007d2f3633

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivity
import Theorems.Thm_GlobalTheory_Hk_LFamPos_norm_lamChi_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LFamPos
namespace GlobalTheory.Hk.LFamPos
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (𝓕.lamChi χ) s := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul (2 : ℂ)
  refine Summable.of_norm_bounded h.norm fun n => ?_
  refine LSeries.norm_term_le s ?_
  refine (norm_lamChi_le 𝓕 χ n).trans (le_of_eq ?_)
  simp [abs_of_nonneg vonMangoldt_nonneg]
end GlobalTheory.Hk.LFamPos
