-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.bRe_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:51:59.787966+00:00
-- url     : https://prove2.me/submissions/a9d40b11-0fdc-4d23-8c9b-1ec0339655b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_chi_real
import Theorems.Thm_GlobalTheory_Hk_RealChar_a_le

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
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (n : ℕ) :
    |bRe 𝓕 χ n| ≤ (Fintype.card 𝓕.G * 14 : ℝ) * n := by
  unfold bRe
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (14 * n : ℝ) fun g _ => ?_).trans (le_of_eq ?_)
  · rw [abs_mul, abs_of_nonneg (𝓕.a_nonneg g n)]
    rcases chi_real h g with e | e <;> simpa [e] using a_le 𝓕 g n
  · simp [mul_assoc]
end GlobalTheory.Hk.RealChar
