-- Prove2me | solution 1 for GlobalTheory.Hk.ZeroFree.inv_le_ell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:01:40.000398+00:00
-- url     : https://prove2.me/submissions/3e5ffa49-642c-483c-8aef-e6ae856f0ff5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionZeroFreeRegion
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_re_one_div
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_re_LSeries_le
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_one_le_ell
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_ell_zero_le
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_ell_two_le
import Theorems.Thm_GlobalTheory_Hk_ZeroFree_pole_le
import Theorems.Thm_GlobalTheory_Hk_LFamPos_positivity
import Theorems.Thm_GlobalTheory_T_rayClassLFunctionFamily_continuation_growth
import Theorems.Thm_GlobalTheory_T_rayClassLFunctionFamily_logDeriv_positivity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
namespace GlobalTheory.Hk.ZeroFree
private lemma norm_ofReal_add_mul_I_le_abs_add_abs (x y : ℝ) : ‖(x : ℂ) + y * I‖ ≤ |x| + |y| := by
  simpa using norm_le_abs_re_add_abs_im ((x : ℂ) + y * I)
end GlobalTheory.Hk.ZeroFree
end

set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.ZeroFree
namespace GlobalTheory.Hk.ZeroFree
theorem _root_.solution : ∃ K : ℝ, 0 < K ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (ε δ γ : ℝ),
    𝓕.F χ (((1 - δ : ℝ) : ℂ) + γ * I) = 0 → (χ * χ ≠ 1 ∨ γ ≠ 0) →
    0 < ε → ε ≤ 1 / 400 → 0 ≤ δ → δ ≤ ε → 1 / ε ≤ K * 𝓕.ell γ := by
  obtain ⟨C, hC, hR⟩ := re_LSeries_le
  refine ⟨300 * C, by positivity, ?_⟩
  intro 𝓕 χ ε δ γ hz hχ hε hε1 hδ hδε
  set ρ : ℂ := ((1 - δ : ℝ) : ℂ) + γ * I with hρ
  have hℓ0 := ell_zero_le 𝓕 γ
  have hℓ2 := ell_two_le 𝓕 γ
  have hℓ1 := one_le_ell 𝓕 γ
  have hCℓ0 : C * 𝓕.ell 0 ≤ C * 𝓕.ell γ := mul_le_mul_of_nonneg_left hℓ0 hC.le
  have hCℓ2 : C * 𝓕.ell (2 * γ) ≤ 2 * (C * 𝓕.ell γ) := by nlinarith
  have hCℓ : 0 ≤ C * 𝓕.ell γ := mul_nonneg hC.le (by linarith)
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 / ε := ⟨_, rfl⟩
  have hv0 : 0 < v := by rw [hv]; positivity
  rw [← hv]
  by_cases hB : χ * χ = 1 ∧ γ ^ 2 < (30 * ε) ^ 2
  · obtain ⟨hχ2, hγ⟩ := hB
    have hγ0 : γ ≠ 0 := hχ.resolve_left (not_not.mpr hχ2)
    have ha0 : 0 < 60 * ε := by positivity
    have ha2 : 60 * ε ≤ 1 / 2 := by linarith
    set ρ' : ℂ := ((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I with hρ'
    have hz' : 𝓕.F χ ρ' = 0 := by
      have hc := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).2.2.2 hχ2 ρ
      have e : (starRingEnd ℂ) ρ = ρ' := by
        rw [hρ, hρ']
        apply Complex.ext <;> simp
      rw [← e, hc, hz]
      simp
    have hne : ρ ≠ ρ' := by
      intro h
      have := congrArg Complex.im h
      simp [hρ, hρ'] at this
      exact hγ0 (by linarith)
    have hγa : |γ| < 30 * ε := abs_lt_of_sq_lt_sq hγ (by linarith)
    have hnorm : ∀ g : ℝ, |g| < 30 * ε →
        ‖(((1 - δ : ℝ) : ℂ) + g * I) - (5 / 4 + ((0 : ℝ) : ℂ) * I)‖ ≤ 3 / 5 := by
      intro g hg
      have e : (((1 - δ : ℝ) : ℂ) + g * I) - (5 / 4 + ((0 : ℝ) : ℂ) * I)
          = ((-(1 / 4 + δ) : ℝ) : ℂ) + g * I := by push_cast; ring
      rw [e]
      refine (norm_ofReal_add_mul_I_le_abs_add_abs _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (by linarith)]
      linarith
    have hnear : ∀ w ∈ ({ρ, ρ'} : Finset ℂ),
        ‖w - (5 / 4 + ((0 : ℝ) : ℂ) * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0 := by
      intro w hw
      rcases Finset.mem_insert.mp hw with h | h
      · rw [h]; exact ⟨hnorm γ hγa, hz⟩
      · rw [Finset.mem_singleton.mp h]
        exact ⟨hnorm (-γ) (by rwa [abs_neg]), hz'⟩
    have hsum : ∑ w ∈ ({ρ, ρ'} : Finset ℂ),
        (1 / (((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - w)).re
        = 2 * ((60 * ε + δ) / ((60 * ε + δ) ^ 2 + γ ^ 2)) := by
      rw [Finset.sum_pair hne]
      have e1 : ((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - ρ
          = ((60 * ε + δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by rw [hρ]; push_cast; ring
      have e2 : ((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - ρ'
          = ((60 * ε + δ : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I := by rw [hρ']; push_cast; ring
      rw [e1, e2, re_one_div, re_one_div, neg_sq]
      ring
    have hP : 60 * ε / ((60 * ε) ^ 2 + (0 : ℝ) ^ 2) ≤ 1 / (60 * ε) := by
      apply le_of_eq
      rw [show (60 * ε) ^ 2 + (0 : ℝ) ^ 2 = 60 * ε * (60 * ε) by ring, div_mul_eq_div_div,
        div_self ha0.ne']
    have e0 : ((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = ((1 + 60 * ε : ℝ) : ℂ) := by
      push_cast; ring
    have hmain : 2 * ((60 * ε + δ) / ((60 * ε + δ) ^ 2 + γ ^ 2))
        ≤ 1 / (60 * ε) + 2 * (C * 𝓕.ell 0) := by
      by_cases h1 : χ = 1
      · have h0 := (GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ (1 + 60 * ε) 0 (by linarith)).2.1
        have hb := hR 𝓕 χ (60 * ε) 0 (1 / (60 * ε)) ha0 ha2 (by positivity) (fun _ => hP)
          {ρ, ρ'} hnear
        rw [hsum, e0, h1] at hb
        have hC0 : 0 ≤ C * 𝓕.ell 0 := mul_nonneg hC.le (by linarith [one_le_ell 𝓕 0])
        linarith
      · have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ (1 + 60 * ε) 0 (by linarith)).2.2 hχ2 hχ2).1
        have hb1 := hR 𝓕 1 (60 * ε) 0 (1 / (60 * ε)) ha0 ha2 (by positivity) (fun _ => hP)
          ∅ (by simp)
        have hb2 := hR 𝓕 χ (60 * ε) 0 0 ha0 ha2 le_rfl (fun h => absurd h h1) {ρ, ρ'} hnear
        rw [hsum, e0] at hb2
        rw [e0, Finset.sum_empty] at hb1
        linarith
    have hlow : 60 / (4621 * ε) ≤ (60 * ε + δ) / ((60 * ε + δ) ^ 2 + γ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 60 * ε + δ - 60 * ε by linarith)
        (show (0 : ℝ) ≤ 61 * ε - (60 * ε + δ) by linarith), mul_pos hε hε]
    have i1 : 1 / (60 * ε) = v / 60 := by rw [hv]; ring
    have i2 : 60 / (4621 * ε) = 60 / 4621 * v := by rw [hv]; ring
    nlinarith
  · have hcase1 : χ = 1 → (30 * ε) ^ 2 ≤ γ ^ 2 := by
      intro h
      by_contra hc
      push_neg at hc
      exact hB ⟨by rw [h, mul_one], hc⟩
    have hcase2 : χ * χ = 1 → (30 * ε) ^ 2 ≤ (2 * γ) ^ 2 := by
      intro h
      have : (30 * ε) ^ 2 ≤ γ ^ 2 := by
        by_contra hc
        push_neg at hc
        exact hB ⟨h, hc⟩
      nlinarith [sq_nonneg γ]
    have ha0 : 0 < 6 * ε := by positivity
    have ha2 : 6 * ε ≤ 1 / 2 := by linarith
    have hP0 : 0 ≤ 1 / 156 * (1 / ε) := by positivity
    have hP1 : 6 * ε / ((6 * ε) ^ 2 + (0 : ℝ) ^ 2) ≤ 1 / (6 * ε) := by
      apply le_of_eq
      rw [show (6 * ε) ^ 2 + (0 : ℝ) ^ 2 = 6 * ε * (6 * ε) by ring, div_mul_eq_div_div,
        div_self ha0.ne']
    have h0 := (GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ (1 + 6 * ε) γ (by linarith)).1
    have hb1 := hR 𝓕 1 (6 * ε) 0 (1 / (6 * ε)) ha0 ha2 (by positivity) (fun _ => hP1) ∅ (by simp)
    have hρn : ∀ w ∈ ({ρ} : Finset ℂ), ‖w - (5 / 4 + γ * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0 := by
      intro w hw
      rw [Finset.mem_singleton.mp hw]
      refine ⟨?_, hz⟩
      have e : ρ - (5 / 4 + γ * I) = ((-(1 / 4 + δ) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by
        rw [hρ]; push_cast; ring
      rw [e]
      refine (norm_ofReal_add_mul_I_le_abs_add_abs _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (by linarith), abs_zero]
      linarith
    have hb2 := hR 𝓕 χ (6 * ε) γ (1 / 156 * (1 / ε)) ha0 ha2 hP0
      (fun h => pole_le hε (hcase1 h)) {ρ} hρn
    have hb3 := hR 𝓕 (χ * χ) (6 * ε) (2 * γ) (1 / 156 * (1 / ε)) ha0 ha2 hP0
      (fun h => pole_le hε (hcase2 h)) ∅ (by simp)
    have e0 : ((1 + 6 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = ((1 + 6 * ε : ℝ) : ℂ) := by
      push_cast; ring
    have e2 : ((1 + 6 * ε : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I
        = ((1 + 6 * ε : ℝ) : ℂ) + 2 * (γ : ℂ) * I := by push_cast; ring
    have e1 : ((1 + 6 * ε : ℝ) : ℂ) + (γ : ℂ) * I - ρ
        = ((6 * ε + δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by rw [hρ]; push_cast; ring
    rw [e0, Finset.sum_empty] at hb1
    rw [e2, Finset.sum_empty] at hb3
    rw [Finset.sum_singleton, e1, re_one_div] at hb2
    have hlow : 1 / (7 * ε) ≤ (6 * ε + δ) / ((6 * ε + δ) ^ 2 + (0 : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (show 6 * ε + δ ≤ 7 * ε by linarith)
        (show (0 : ℝ) ≤ 6 * ε + δ by linarith)]
    have i1 : 1 / (6 * ε) = v / 6 := by rw [hv]; ring
    have i2 : 1 / (7 * ε) = v / 7 := by rw [hv]; ring
    have i3 : 1 / 156 * (1 / ε) = v / 156 := by rw [hv]; ring
    nlinarith
end GlobalTheory.Hk.ZeroFree
