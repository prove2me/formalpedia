-- Prove2me | solution 1 for GlobalTheory.Hk.ZeroFree.re_LSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:15:54.679891+00:00
-- url     : https://prove2.me/submissions/e8d7454d-5b27-439d-9fbf-3cf9db939654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionZeroFreeRegion
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_re_one_div
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_re_le_one
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_one_le_order
import Theorems.Thm_GlobalTheory_T_rayClassFamily_logDeriv_re_gt_one
import Theorems.Thm_GlobalTheory_T_rayClassLFunction_logDeriv_local_formula


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
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (a t P : ℝ),
    0 < a → a ≤ 1 / 2 → 0 ≤ P → (χ = 1 → a / (a ^ 2 + t ^ 2) ≤ P) → ∀ S : Finset ℂ,
    (∀ w ∈ S, ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0) →
    (LSeries (𝓕.lamChi χ) (((1 + a : ℝ) : ℂ) + t * I)).re
      ≤ P + C * 𝓕.ell t - ∑ w ∈ S, (1 / (((1 + a : ℝ) : ℂ) + t * I - w)).re := by
  obtain ⟨C, hC, hCb⟩ := GlobalTheory.T.rayClassLFunction_logDeriv_local_formula
  refine ⟨C, hC, ?_⟩
  intro 𝓕 χ a t P ha ha2 hP hχ S hS
  obtain ⟨hfin, -, hD⟩ := hCb 𝓕 χ t
  set s : ℂ := ((1 + a : ℝ) : ℂ) + t * I with hs
  have hsre : s.re = 1 + a := by simp [hs]
  have hsre1 : 1 < s.re := by rw [hsre]; linarith
  obtain ⟨-, -, hFne, hL⟩ := GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ s hsre1
  have hsd : ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 := by
    have e : s - (5 / 4 + t * I) = ((a - 1 / 4 : ℝ) : ℂ) := by rw [hs]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hE := hD s hsd hFne
  have hfpos : ∀ w, 𝓕.F χ w = 0 → 0 ≤ (1 / (s - w)).re := by
    intro w hw
    rw [one_div, inv_re]
    apply div_nonneg _ (normSq_nonneg _)
    rw [sub_re, hsre]
    linarith [re_le_one hw]
  have hsum : (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0},
      (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)).re
      = ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (1 / (s - w)).re := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, re_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [div_eq_mul_one_div, ← ofReal_natCast, re_ofReal_mul]
  have hSZ : ∑ w ∈ S, (1 / (s - w)).re
      ≤ ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (1 / (s - w)).re := by
    calc ∑ w ∈ S, (1 / (s - w)).re
        ≤ ∑ w ∈ S, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (1 / (s - w)).re := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨hw1, hw2⟩ := hS w hw
          have hre : 1 / 2 < w.re := by
            have h1 := (abs_le.mp ((abs_re_le_norm _).trans hw1)).1
            simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at h1
            norm_num at h1
            linarith
          have hm : (1 : ℝ) ≤ analyticOrderNatAt (𝓕.F χ) w := by
            exact_mod_cast one_le_order hre hw2
          nlinarith [hfpos w hw2]
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro w hw
            rw [Set.Finite.mem_toFinset]
            exact hS w hw
          · intro w hw _
            exact mul_nonneg (Nat.cast_nonneg _) (hfpos w ((Set.Finite.mem_toFinset hfin).mp hw).2)
  have hpole : (if χ = 1 then 1 / (s - 1) else 0 : ℂ).re ≤ P := by
    split_ifs with h1
    · have e : s - 1 = (a : ℂ) + t * I := by rw [hs]; push_cast; ring
      rw [e, re_one_div]
      exact hχ h1
    · simpa using hP
  rw [← hL, add_re, neg_re]
  have hre := (abs_le.mp ((abs_re_le_norm _).trans hE)).1
  rw [sub_re, hsum] at hre
  linarith
end GlobalTheory.Hk.ZeroFree
