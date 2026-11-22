-- Prove2me | solution 1 for MasulloRH.full_strip_resolvent_norm_summable_at_three
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T03:33:24.645332+00:00
-- url     : https://prove2.me/submissions/f897972e-84e6-4094-9bb5-3615ddd38028

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open MasulloRH

private theorem resolvent_bound (ρ : ZetaZerosInTraceStrip (1 / 2)) :
    ‖zeroResolventTerm (1 / 2) (3 : ℂ) ρ‖ ≤ zeroDecayWeight (1 / 2) ρ := by
  let β : ℝ := ρ.val.re
  let γ : ℝ := ρ.val.im
  have hβ0 : 0 < β := by simpa [β] using ρ.property.2.1
  have hβ1 : β < 1 := by simpa [β] using ρ.property.2.2.1
  have h1 : (3 : ℂ) - (ρ : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.sub_re] at hr
    nlinarith
  have h2 : (5 / 2 : ℂ) - (ρ : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.sub_re] at hr
    nlinarith
  have hdiff :
      1 / ((3 : ℂ) - (ρ : ℂ)) - 1 / ((5 / 2 : ℂ) - (ρ : ℂ)) =
        (((5 / 2 : ℂ) - (ρ : ℂ)) - ((3 : ℂ) - (ρ : ℂ))) /
          (((3 : ℂ) - (ρ : ℂ)) * ((5 / 2 : ℂ) - (ρ : ℂ))) := by
    simp only [one_div]
    exact inv_sub_inv h1 h2
  let A : ℝ := ‖(3 : ℂ) - (ρ : ℂ)‖
  let B : ℝ := ‖(5 / 2 : ℂ) - (ρ : ℂ)‖
  have hA2 : A ^ 2 = (3 - β) ^ 2 + γ ^ 2 := by
    dsimp [A, β, γ]
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.sub_re, Complex.sub_im]
    ring
  have hB2 : B ^ 2 = (5 / 2 - β) ^ 2 + γ ^ 2 := by
    dsimp [B, β, γ]
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.sub_re, Complex.sub_im]
    ring
  have hA2lb : 4 + γ ^ 2 ≤ A ^ 2 := by
    rw [hA2]
    nlinarith
  have hB2lb : 9 / 4 + γ ^ 2 ≤ B ^ 2 := by
    rw [hB2]
    nlinarith
  have hAB : (1 + γ ^ 2) / 2 ≤ A * B := by
    have hA : 0 ≤ A := norm_nonneg _
    have hB : 0 ≤ B := norm_nonneg _
    have hprod : (4 + γ ^ 2) * (9 / 4 + γ ^ 2) ≤ (A * B) ^ 2 := by
      nlinarith [mul_le_mul hA2lb hB2lb (by positivity : 0 ≤ 9 / 4 + γ ^ 2) (sq_nonneg A)]
    have hbase : ((1 + γ ^ 2) / 2) ^ 2 ≤ (4 + γ ^ 2) * (9 / 4 + γ ^ 2) := by
      nlinarith [sq_nonneg (γ ^ 2)]
    apply (sq_le_sq₀ (by positivity) (mul_nonneg hA hB)).mp
    nlinarith [hbase, hprod]
  have hnum : ‖(((5 / 2 : ℂ) - (ρ : ℂ)) - ((3 : ℂ) - (ρ : ℂ)))‖ = (1 / 2 : ℝ) := by
    norm_num [Complex.norm_real]
  have hterm : ‖1 / ((3 : ℂ) - (ρ : ℂ)) - 1 / ((5 / 2 : ℂ) - (ρ : ℂ))‖ ≤
      1 / (1 + γ ^ 2) := by
    rw [hdiff, norm_div, Complex.norm_mul, hnum]
    have hA : 0 ≤ A := norm_nonneg _
    have hB : 0 ≤ B := norm_nonneg _
    have hApos : 0 < A := by nlinarith [hA2lb, sq_nonneg γ]
    have hBpos : 0 < B := by nlinarith [hB2lb, sq_nonneg γ]
    have hden : 0 < A * B := mul_pos hApos hBpos
    exact (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by positivity : (0 : ℝ) < (1 + γ ^ 2) / 2) hAB).trans_eq (by
        field_simp)
  rw [zeroResolventTerm, Complex.norm_mul]
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := by positivity
  have hmnorm : ‖(analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ)‖ =
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := by
    rw [show (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) =
      ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) : ℂ) by norm_num]
    rw [Complex.norm_real]
    exact abs_of_nonneg hm
  rw [hmnorm]
  simpa [zeroDecayWeight, γ, div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_left hterm hm)

theorem solution :
    Summable (fun ρ : ZetaZerosInTraceStrip (1 / 2) =>
      ‖zeroResolventTerm (1 / 2) (3 : ℂ) ρ‖) := by
  apply Summable.of_norm_bounded (weighted_zero_summability (1 / 2) (by norm_num))
  intro ρ
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using resolvent_bound ρ



