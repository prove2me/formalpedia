-- Prove2me | solution 1 for GlobalTheory.ZeroFreeComplex.inv_le_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:20.68416+00:00
-- url     : https://prove2.me/submissions/c1ceab59-6cad-456d-9259-3b41c05b2e64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_LFunction_conj_eq_zero
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_neg_re_logDeriv_le
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_re_one_div
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_half_lt_log
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_log_zero_le
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_log_two_le
import Theorems.Thm_GlobalTheory_PrincipalLogDeriv_neg_re_logDeriv_le
import Theorems.Thm_GlobalTheory_TwoRealCharacters_neg_sum_logDeriv_nonneg
import Theorems.Thm_GlobalTheory_logDerivativeThreeFourOne_three_four_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
namespace GlobalTheory.ZeroFreeComplex
private theorem norm_ofReal_add_mul_I_le_of_sq_add_sq_le (a b r : ℝ) (hr : 0 ≤ r) (h : a ^ 2 + b ^ 2 ≤ r ^ 2) :
    ‖(a : ℂ) + b * I‖ ≤ r := by
  have h1 : ‖(a : ℂ) + b * I‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  nlinarith [norm_nonneg ((a : ℂ) + b * I)]
end GlobalTheory.ZeroFreeComplex
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ZeroFreeComplex
namespace GlobalTheory.ZeroFreeComplex
theorem _root_.solution : ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ γ : ℝ), χ ≠ 1 → LFunction χ (((1 - δ : ℝ) : ℂ) + γ * I) = 0 → (χ ^ 2 ≠ 1 ∨ γ ≠ 0) →
    0 < δ → δ ≤ 1 / 21 → 1 / δ ≤ K * Real.log (q * (|γ| + 2)) := by
  obtain ⟨C1, hC1, h1⟩ := neg_re_logDeriv_le
  obtain ⟨C0, hC0, h0⟩ := GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le
  refine ⟨300 * (C0 + C1), by positivity, fun q _ χ δ γ hχ hρ hcase hδ hδ21 => ?_⟩
  have hLpos : 0 < Real.log (q * (|γ| + 2)) := by linarith [half_lt_log q γ]
  have hL0 := log_zero_le q γ
  have hL2 := log_two_le q γ
  set L := Real.log (q * (|γ| + 2)) with hL_def
  have hC0L : 0 < C0 * L := mul_pos hC0 hLpos
  have hC1L : 0 < C1 * L := mul_pos hC1 hLpos
  have hσ1 : 1 < 1 + 8 * δ := by linarith
  have hσ2 : 1 + 8 * δ ≤ 2 := by linarith
  have hA : -(deriv (LFunction (1 : DirichletCharacter ℂ q)) ((1 + 8 * δ : ℝ) : ℂ) /
      LFunction (1 : DirichletCharacter ℂ q) ((1 + 8 * δ : ℝ) : ℂ)).re ≤ 1 / δ / 8 + C0 * L := by
    have h := h0 q (1 + 8 * δ) 0 hσ1 hσ2
    rw [show (((1 + 8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 8 * δ : ℝ) : ℂ) by simp] at h
    rw [show ((1 + 8 * δ : ℝ) : ℂ) - 1 = ((8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I by push_cast; ring,
      re_one_div] at h
    have e : 8 * δ / ((8 * δ) ^ 2 + 0 ^ 2) = 1 / δ / 8 := by field_simp; ring
    rw [e] at h
    have hk : C0 * Real.log (q * (|(0 : ℝ)| + 2)) ≤ C0 * L := mul_le_mul_of_nonneg_left hL0 hC0.le
    simp only [abs_zero, zero_add] at h hk
    linarith
  have hρ3 : ‖(((1 - δ : ℝ) : ℂ) + γ * I) - (3/2 + γ * I)‖ ≤ 5/6 := by
    rw [show (((1 - δ : ℝ) : ℂ) + γ * I) - (3/2 + γ * I) = ((-(1/2) - δ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hB : -(deriv (LFunction χ) (((1 + 8 * δ : ℝ) : ℂ) + γ * I) /
      LFunction χ (((1 + 8 * δ : ℝ) : ℂ) + γ * I)).re ≤ C1 * L - 1 / δ / 9 := by
    have h := h1 q χ hχ (1 + 8 * δ) γ hσ1 hσ2 {((1 - δ : ℝ) : ℂ) + γ * I} (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      rw [hw]
      exact ⟨hρ3, hρ⟩)
    rw [Finset.sum_singleton, show ((1 + 8 * δ : ℝ) : ℂ) + γ * I - (((1 - δ : ℝ) : ℂ) + γ * I) =
      ((9 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I by push_cast; ring, re_one_div] at h
    have e : 9 * δ / ((9 * δ) ^ 2 + 0 ^ 2) = 1 / δ / 9 := by field_simp; ring
    rw [e] at h
    exact h
  have hxpos : 0 < 1 / δ := by positivity
  by_cases h2 : χ ^ 2 = 1
  · have hγ : γ ≠ 0 := hcase.resolve_left (not_not.mpr h2)
    by_cases hsmall : 2 * γ ^ 2 ≤ 81 * δ ^ 2
    · have hcρ : LFunction χ (conj (((1 - δ : ℝ) : ℂ) + γ * I)) = 0 := LFunction_conj_eq_zero hχ h2 hρ
      have hconj : conj (((1 - δ : ℝ) : ℂ) + γ * I) = ((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [hconj] at hcρ
      have hne : ((1 - δ : ℝ) : ℂ) + γ * I ≠ ((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by
        intro h
        have := congrArg Complex.im h
        simp at this
        exact hγ (by linarith)
      have hdisk : ∀ w ∈ ({((1 - δ : ℝ) : ℂ) + γ * I, ((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I} :
          Finset ℂ), ‖w - (3/2 + ((0 : ℝ) : ℂ) * I)‖ ≤ 5/6 ∧ LFunction χ w = 0 := by
        intro w hw
        rcases Finset.mem_insert.mp hw with hw | hw
        · rw [hw]
          refine ⟨?_, hρ⟩
          rw [show (((1 - δ : ℝ) : ℂ) + γ * I) - (3/2 + ((0 : ℝ) : ℂ) * I) =
            ((-(1/2) - δ : ℝ) : ℂ) + (γ : ℂ) * I by push_cast; ring]
          exact norm_ofReal_add_mul_I_le_of_sq_add_sq_le _ _ _ (by norm_num) (by nlinarith)
        · rw [Finset.mem_singleton] at hw
          rw [hw]
          refine ⟨?_, hcρ⟩
          rw [show (((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I) - (3/2 + ((0 : ℝ) : ℂ) * I) =
            ((-(1/2) - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I by push_cast; ring]
          exact norm_ofReal_add_mul_I_le_of_sq_add_sq_le _ _ _ (by norm_num) (by nlinarith)
      have h := h1 q χ hχ (1 + 8 * δ) 0 hσ1 hσ2 _ hdisk
      rw [Finset.sum_pair hne] at h
      rw [show ((1 + 8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - (((1 - δ : ℝ) : ℂ) + γ * I) =
          ((9 * δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I by push_cast; ring,
        show ((1 + 8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - (((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I) =
          ((9 * δ : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I by push_cast; ring,
        re_one_div, re_one_div,
        show (((1 + 8 * δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 8 * δ : ℝ) : ℂ) by simp] at h
      simp only [abs_zero, zero_add] at h
      set T := 9 * δ / ((9 * δ) ^ 2 + γ ^ 2) with hT
      have hlow : 2 / 27 * (1 / δ) ≤ T := by
        rw [hT]
        rw [div_mul_eq_mul_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      rw [neg_sq] at h
      have H := GlobalTheory.TwoRealCharacters.neg_sum_logDeriv_nonneg q χ χ (1 + 8 * δ) h2 h2 hσ1
      rw [show χ * χ = 1 by rw [← sq]; exact h2] at H
      have hk : C1 * Real.log (q * (|(0 : ℝ)| + 2)) ≤ C1 * L := mul_le_mul_of_nonneg_left hL0 hC1.le
      simp only [abs_zero, zero_add] at hk
      have hb : -(deriv (LFunction χ) ((1 + 8 * δ : ℝ) : ℂ) / LFunction χ ((1 + 8 * δ : ℝ) : ℂ)).re
          ≤ C1 * L - 4 / 27 * (1 / δ) := by linarith
      linarith
    · push Not at hsmall
      have hC : -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (((1 + 8 * δ : ℝ) : ℂ) + 2 * γ * I) /
          LFunction (1 : DirichletCharacter ℂ q) (((1 + 8 * δ : ℝ) : ℂ) + 2 * γ * I)).re
          ≤ 4 / 81 * (1 / δ) + 2 * C0 * L := by
        have h := h0 q (1 + 8 * δ) (2 * γ) hσ1 hσ2
        rw [show ((1 + 8 * δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I - 1 =
          ((8 * δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I by push_cast; ring, re_one_div] at h
        have e : 8 * δ / ((8 * δ) ^ 2 + (2 * γ) ^ 2) ≤ 4 / 81 * (1 / δ) := by
          rw [div_mul_eq_mul_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        push_cast at h ⊢
        linarith [mul_le_mul_of_nonneg_left hL2 hC0.le]
      have H := GlobalTheory.logDerivativeThreeFourOne.three_four_one q χ (1 + 8 * δ) γ hσ1
      rw [h2] at H
      push_cast at H hA hB hC
      linarith
  · have hC : -(deriv (LFunction (χ ^ 2)) (((1 + 8 * δ : ℝ) : ℂ) + 2 * γ * I) /
        LFunction (χ ^ 2) (((1 + 8 * δ : ℝ) : ℂ) + 2 * γ * I)).re ≤ 2 * C1 * L := by
      have h := h1 q (χ ^ 2) h2 (1 + 8 * δ) (2 * γ) hσ1 hσ2 ∅ (by simp)
      rw [Finset.sum_empty, sub_zero] at h
      push_cast at h ⊢
      linarith [mul_le_mul_of_nonneg_left hL2 hC1.le]
    have H := GlobalTheory.logDerivativeThreeFourOne.three_four_one q χ (1 + 8 * δ) γ hσ1
    push_cast at H hA hB hC
    linarith
end GlobalTheory.ZeroFreeComplex
