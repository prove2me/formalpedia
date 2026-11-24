-- Prove2me | solution 1 for GlobalTheory.T.exists_rayClassLFunction_real_zero_far_from_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:33.718689+00:00
-- url     : https://prove2.me/submissions/8e237b1a-4830-40e4-a712-4772c866f02c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsRayClassLFunctionRealZeroFarFromOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsRayClassLFunctionRealZeroFarFromOneStatement
import Theorems.Thm_GlobalTheory_Hk_LFam_real_zero_far_from_one


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
theorem _root_.solution : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (β : ℝ), χ * χ = 1 → 3 / 4 ≤ β → 𝓕.F χ β = 0 → c / 𝓕.B ^ A ≤ 1 - β := by
  first | exact @GlobalTheory.Hk.LFam.real_zero_far_from_one | exact GlobalTheory.Hk.LFam.real_zero_far_from_one | (intros; apply GlobalTheory.Hk.LFam.real_zero_far_from_one <;> assumption)
end _root_.GlobalTheory.T
