-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.res_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:21.557793+00:00
-- url     : https://prove2.me/submissions/27ea8988-8158-4e24-9484-d109d91279a9

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
theorem _root_.solution : 𝓕.res χ = ∑ g, χ g * (𝓕.κ : ℂ) := by
  rw [← Finset.sum_mul, AddChar.sum_eq_ite, LFam.res, AddChar.one_eq_zero]
  split_ifs <;> simp [mul_comm]
end GlobalTheory.Hk.RayCont
