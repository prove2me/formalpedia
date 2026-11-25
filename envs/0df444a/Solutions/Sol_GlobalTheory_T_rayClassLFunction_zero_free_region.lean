-- Prove2me | solution 1 for GlobalTheory.T.rayClassLFunction_zero_free_region
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:28:24.534091+00:00
-- url     : https://prove2.me/submissions/fe73d0a4-8be8-467b-b87d-342a18391610

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionZeroFreeRegion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionZeroFreeRegionStatement
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_zero_free_region


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 3 / 4 ≤ s.re → 𝓕.F χ s = 0 → (χ * χ ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / 𝓕.ell s.im := by
  first | exact @GlobalTheory.Hk.ZeroFree.zero_free_region | exact GlobalTheory.Hk.ZeroFree.zero_free_region | (intros; apply GlobalTheory.Hk.ZeroFree.zero_free_region <;> assumption)
end _root_.GlobalTheory.T
