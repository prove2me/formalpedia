-- Prove2me | solution 1 for GlobalTheory.Hk.ZeroFree.zero_free_region
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:12:35.678949+00:00
-- url     : https://prove2.me/submissions/a1e78850-2d02-4f0b-b70a-392304af5336

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionZeroFreeRegion
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_re_le_one
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_inv_le_ell
import Theorems.Thm_GlobalTheory_Hk_LFamPos_positivity
import Theorems.Thm_GlobalTheory_Hk_LFam_two_lt_ell


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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.ZeroFree
namespace GlobalTheory.Hk.ZeroFree
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 3 / 4 ≤ s.re → 𝓕.F χ s = 0 → (χ * χ ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / 𝓕.ell s.im := by
  obtain ⟨K, hK, hKb⟩ := inv_le_ell
  refine ⟨1 / (4 * K + 400), by positivity, ?_⟩
  intro 𝓕 χ s _ hs hχ
  by_contra hlt
  push_neg at hlt
  have hℓ2 := 𝓕.two_lt_ell s.im
  have hℓpos : 0 < 𝓕.ell s.im := by linarith
  have hpos : 0 < (2 * K + 200) * 𝓕.ell s.im := mul_pos (by linarith) hℓpos
  have hε : 0 < 1 / ((2 * K + 200) * 𝓕.ell s.im) := by positivity
  have hε1 : 1 / ((2 * K + 200) * 𝓕.ell s.im) ≤ 1 / 400 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [mul_pos hK hℓpos]
  have hδ : 0 ≤ 1 - s.re := by linarith [re_le_one hs]
  have hδε : 1 - s.re ≤ 1 / ((2 * K + 200) * 𝓕.ell s.im) := by
    have h1 : 1 - s.re ≤ 1 / (4 * K + 400) / 𝓕.ell s.im := by linarith
    refine h1.trans ?_
    rw [div_div]
    apply one_div_le_one_div_of_le hpos
    nlinarith [mul_pos hK hℓpos]
  have hz : 𝓕.F χ (((1 - (1 - s.re) : ℝ) : ℂ) + s.im * I) = 0 := by
    rw [show (1 - (1 - s.re) : ℝ) = s.re by ring, re_add_im]
    exact hs
  have h := hKb 𝓕 χ _ (1 - s.re) s.im hz hχ hε hε1 hδ hδε
  rw [one_div_one_div] at h
  nlinarith [mul_pos hK hℓpos]
end GlobalTheory.Hk.ZeroFree
