-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.norm_res_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:20.689147+00:00
-- url     : https://prove2.me/submissions/7cb6822e-c840-4f9c-a453-95fd2404dc81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution : ‖𝓕.res χ‖ ≤ 4 * 𝓕.B := by
  have hB := 𝓕.B_ge
  have hκ : 0 ≤ 𝓕.κ := le_trans (by positivity) 𝓕.κ_ge
  rw [LFam.res]
  split_ifs
  · rw [norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)
  · rw [norm_zero]
    positivity
end GlobalTheory.Hk.RayCont
