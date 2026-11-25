-- Prove2me | solution 1 for GlobalTheory.Hk.RealZero.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:34:27.948417+00:00
-- url     : https://prove2.me/submissions/fbdb8cbb-3d60-4621-b11d-a557f12344e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionUniqueSimpleExceptionalZero
import Theorems.Thm_GlobalTheory_Hk_RealZero_le_order
import Theorems.Thm_GlobalTheory_Hk_RealZero_re_le_one
import Theorems.Thm_GlobalTheory_Hk_RealZero_exists_bound
import Theorems.Thm_GlobalTheory_Hk_LFamPos_positivity
import Theorems.Thm_GlobalTheory_Hk_LFam_two_lt_ell
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
namespace GlobalTheory.Hk.RealZero
private lemma term_lemma_3 {c ℓ σ β : ℝ} (m : ℝ) (hm : 0 ≤ m) (hc : 0 < c) (hℓ : 0 < ℓ)
    (hσ : σ = 1 + 2 * c / ℓ) (h1 : 1 - c / ℓ ≤ β) (h2 : β ≤ 1) :
    m * (ℓ / (3 * c)) ≤ m / (σ - β) := by
  subst hσ
  have h2c : 0 < 2 * c / ℓ := by positivity
  have hpos : 0 < 1 + 2 * c / ℓ - β := by linarith
  have hle : 1 + 2 * c / ℓ - β ≤ 3 * c / ℓ := by
    have : 3 * c / ℓ = c / ℓ + 2 * c / ℓ := by ring
    linarith
  have key := one_div_le_one_div_of_le hpos hle
  rw [one_div_div] at key
  rw [div_eq_mul_one_div m]
  exact mul_le_mul_of_nonneg_left key hm
private lemma false_of_le_of_mul_hundred_mul_add_one_eq_one {C c ℓ X : ℝ} (hC : 0 < C) (hℓ : 0 < ℓ) (hcC : c * (100 * (C + 1)) = 1)
    (hc : 0 < c) (hX : 2 * (ℓ / (3 * c)) ≤ X) (h : 0 ≤ ℓ / (2 * c) + 4 * (C * ℓ) - X) : False := by
  have h1c : 1 / c = 100 * (C + 1) := by
    rw [eq_comm, eq_div_iff hc.ne']
    linear_combination hcC
  have e2 : ℓ / (2 * c) = ℓ / 2 * (1 / c) := by rw [div_mul_div_comm, mul_one]
  have e3 : ℓ / (3 * c) = ℓ / 3 * (1 / c) := by rw [div_mul_div_comm, mul_one]
  rw [e3, h1c] at hX
  rw [e2, h1c] at h
  nlinarith [mul_pos hℓ hC]
end GlobalTheory.Hk.RealZero
end

set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealZero
namespace GlobalTheory.Hk.RealZero
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (β β' : ℝ), χ * χ = 1 → ψ * ψ = 1 → 3 / 4 ≤ β → 3 / 4 ≤ β' → 1 - c / 𝓕.ell 0 ≤ β → 1 - c / 𝓕.ell 0 ≤ β' → 𝓕.F χ β = 0 → 𝓕.F ψ β' = 0 → χ = ψ ∧ β = β' ∧ deriv (𝓕.F χ) β ≠ 0 := by
  obtain ⟨C, hC, hb⟩ := exists_bound
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (100 * (C + 1)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hcC : c * (100 * (C + 1)) = 1 := by
    rw [hcdef, one_div, inv_mul_cancel₀ (by positivity)]
  refine ⟨c, hc, ?_⟩
  intro 𝓕 χ ψ β β' hχ hψ hβ hβ' hc1 hc1' hz hz'
  have hℓ2 : 2 < 𝓕.ell 0 := 𝓕.two_lt_ell 0
  have hℓ : 0 < 𝓕.ell 0 := by linarith
  have hCℓ : 0 < C * 𝓕.ell 0 := mul_pos hC hℓ
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + 2 * c / 𝓕.ell 0 := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by
    have : 0 < 2 * c / 𝓕.ell 0 := by positivity
    linarith
  have hσ2 : σ ≤ 7 / 4 := by
    have hc' : c < 1 / 100 := by nlinarith [mul_pos hc hC]
    have : 2 * c / 𝓕.ell 0 ≤ 3 / 4 := by
      rw [div_le_iff₀ hℓ]
      linarith
    linarith
  have hpole : 1 / (σ - 1) = 𝓕.ell 0 / (2 * c) := by
    rw [hσdef, add_sub_cancel_left, one_div_div]
  have hq : 0 < 𝓕.ell 0 / (3 * c) := by positivity
  have tb : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ) (k : ℕ), 3 / 4 ≤ x → 1 - c / 𝓕.ell 0 ≤ x →
      𝓕.F φ x = 0 → (∀ i < k, iteratedDeriv i (𝓕.F φ) x = 0) →
      k * (𝓕.ell 0 / (3 * c)) ≤ (analyticOrderNatAt (𝓕.F φ) x : ℝ) / (σ - x) := by
    intro φ x k hx hxc hx0 hk
    have hx2 : 1 / 2 < (x : ℂ).re := by
      rw [Complex.ofReal_re]
      linarith
    have hx1 : x ≤ 1 := by simpa using re_le_one 𝓕 φ hx0
    have hm : (k : ℝ) ≤ analyticOrderNatAt (𝓕.F φ) x := by
      exact_mod_cast le_order 𝓕 φ hx2 k hk
    have ht := term_lemma_3 (analyticOrderNatAt (𝓕.F φ) x : ℝ) (by positivity) hc hℓ hσdef hxc hx1
    nlinarith
  have d1 : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ), 𝓕.F φ x = 0 → ∀ i < 1, iteratedDeriv i (𝓕.F φ) x = 0 := by
    intro φ x h0 i hi
    interval_cases i
    simpa using h0
  have tβ := tb χ β 1 hβ hc1 hz (d1 χ β hz)
  have tβ' := tb ψ β' 1 hβ' hc1' hz' (d1 ψ β' hz')
  push_cast at tβ tβ'
  have sg : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ), 3 / 4 ≤ x → 𝓕.F φ x = 0 →
      ∀ y ∈ ({x} : Finset ℝ), 3 / 4 ≤ y ∧ 𝓕.F φ y = 0 := by
    intro φ x hx h0 y hy
    rw [Finset.mem_singleton] at hy
    rw [hy]
    exact ⟨hx, h0⟩
  by_cases hcp : χ = ψ
  · subst hcp
    refine ⟨rfl, ?_⟩
    by_contra hbad
    obtain ⟨T, hT, hXT⟩ : ∃ T : Finset ℝ, (∀ x ∈ T, 3 / 4 ≤ x ∧ 𝓕.F χ x = 0) ∧
        2 * (𝓕.ell 0 / (3 * c)) ≤ ∑ x ∈ T, (analyticOrderNatAt (𝓕.F χ) x : ℝ) / (σ - x) := by
      by_cases hne : β = β'
      · have hd : deriv (𝓕.F χ) β = 0 := by
          by_contra hd
          exact hbad ⟨hne, hd⟩
        refine ⟨{β}, sg χ β hβ hz, ?_⟩
        rw [Finset.sum_singleton]
        have h2 := tb χ β 2 hβ hc1 hz (by
          intro i hi
          interval_cases i
          · simpa using hz
          · simpa using hd)
        exact_mod_cast h2
      · refine ⟨{β, β'}, ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨hβ, hz⟩
          · exact ⟨hβ', hz'⟩
        · rw [Finset.sum_pair hne]
          linarith
    by_cases h1 : χ = 1
    · subst h1
      have hB := hb 𝓕 1 σ hσ1 hσ2 T hT
      rw [if_pos rfl, hpole] at hB
      have h0 := (GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 1 1 σ 0 hσ1).2.1
      exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc hXT (by linarith)
    · have hB := hb 𝓕 χ σ hσ1 hσ2 T hT
      rw [if_neg h1] at hB
      have hB1 := hb 𝓕 1 σ hσ1 hσ2 ∅ (by simp)
      rw [if_pos rfl, hpole, Finset.sum_empty] at hB1
      have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ σ 0 hσ1).2.2 hχ hχ).1
      exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc hXT (by linarith)
  · exfalso
    by_cases h1 : χ = 1
    · subst h1
      have hψ1 : ψ ≠ 1 := fun h => hcp h.symm
      have hB1 := hb 𝓕 1 σ hσ1 hσ2 {β} (sg 1 β hβ hz)
      rw [if_pos rfl, hpole, Finset.sum_singleton] at hB1
      have hBψ := hb 𝓕 ψ σ hσ1 hσ2 {β'} (sg ψ β' hβ' hz')
      rw [if_neg hψ1, Finset.sum_singleton] at hBψ
      have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 ψ ψ σ 0 hσ1).2.2 hψ hψ).1
      exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F 1) β : ℝ) / (σ - β) +
        (analyticOrderNatAt (𝓕.F ψ) β' : ℝ) / (σ - β')) (by linarith) (by linarith)
    · by_cases h2 : ψ = 1
      · subst h2
        have hB1 := hb 𝓕 1 σ hσ1 hσ2 {β'} (sg 1 β' hβ' hz')
        rw [if_pos rfl, hpole, Finset.sum_singleton] at hB1
        have hBχ := hb 𝓕 χ σ hσ1 hσ2 {β} (sg χ β hβ hz)
        rw [if_neg h1, Finset.sum_singleton] at hBχ
        have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ σ 0 hσ1).2.2 hχ hχ).1
        exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) +
          (analyticOrderNatAt (𝓕.F 1) β' : ℝ) / (σ - β')) (by linarith) (by linarith)
      · have hχψ : χ * ψ ≠ 1 := by
          intro h
          apply hcp
          calc χ = χ * (ψ * ψ) := by rw [hψ, mul_one]
            _ = (χ * ψ) * ψ := (mul_assoc _ _ _).symm
            _ = ψ := by rw [h, one_mul]
        have hB1 := hb 𝓕 1 σ hσ1 hσ2 ∅ (by simp)
        rw [if_pos rfl, hpole, Finset.sum_empty] at hB1
        have hBχ := hb 𝓕 χ σ hσ1 hσ2 {β} (sg χ β hβ hz)
        rw [if_neg h1, Finset.sum_singleton] at hBχ
        have hBψ := hb 𝓕 ψ σ hσ1 hσ2 {β'} (sg ψ β' hβ' hz')
        rw [if_neg h2, Finset.sum_singleton] at hBψ
        have hBχψ := hb 𝓕 (χ * ψ) σ hσ1 hσ2 ∅ (by simp)
        rw [if_neg hχψ, Finset.sum_empty] at hBχψ
        have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ ψ σ 0 hσ1).2.2 hχ hψ).2
        exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) +
          (analyticOrderNatAt (𝓕.F ψ) β' : ℝ) / (σ - β')) (by linarith) (by linarith)
end GlobalTheory.Hk.RealZero
