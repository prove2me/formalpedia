-- Prove2me | solution 1 for GlobalTheory.Hk.LogDeriv.aChi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:14.670082+00:00
-- url     : https://prove2.me/submissions/9a004a4c-33e5-49fe-98a6-5acd8d579fb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.LogDeriv
theorem _root_.solution : 𝓕.aChi χ 1 = 1 := by
  show ∑ g, χ g * (𝓕.a g 1 : ℂ) = 1
  rw [Finset.sum_eq_single (0 : 𝓕.G)]
  · rw [AddChar.map_zero_eq_one, 𝓕.a_one]
    simp
  · intro g _ hg
    rw [𝓕.a_one_ne g hg]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h
end GlobalTheory.Hk.LogDeriv
