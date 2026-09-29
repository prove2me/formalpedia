-- Prove2me | solution 1 for LanglandsTunnell.principal_profile_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c34bd62f-d213-5786-a8e2-745015ad1562

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Theorems.Thm_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_principal_profile_exists_ne_zero

set_option autoImplicit false
open scoped Real
open MeasureTheory Set
open LanglandsTunnell

theorem solution (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2)
    (c : ℂ) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = (y : ℂ) ^ (1 / 2 - c) *
      ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) :
    ∃ y : ℝ, 0 < y ∧ f y ≠ 0 := by
  by_contra hcon
  push Not at hcon

  have hW : ∀ y : ℝ, 0 < y → ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
      ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
        (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) = 0 := by
    intro y hy
    have h := hcon y hy
    rw [hf y] at h
    rcases mul_eq_zero.1 h with h0 | h0
    · exfalso
      rw [Complex.cpow_eq_zero_iff] at h0
      exact Complex.ofReal_ne_zero.2 hy.ne' h0.1
    · exact h0

  set σ : ℝ := 1 + |(u₁ + signShift a₁).re| + |(u₂ + signShift a₂).re| with hσ
  have h₁ : 0 < ((σ : ℂ) + (u₁ + signShift a₁)).re := by
    rw [Complex.add_re, Complex.ofReal_re, hσ]
    linarith [neg_abs_le (u₁ + signShift a₁).re, abs_nonneg (u₂ + signShift a₂).re]
  have h₂ : 0 < ((σ : ℂ) + (u₂ + signShift a₂)).re := by
    rw [Complex.add_re, Complex.ofReal_re, hσ]
    linarith [neg_abs_le (u₂ + signShift a₂).re, abs_nonneg (u₁ + signShift a₁).re]
  have hid := LanglandsTunnell.mellin_mulConvGaussian_eq_archFactor_principal u₁ a₁ u₂ a₂ σ h₁ h₂

  have hL : mellin (fun y : ℝ => (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
      (σ : ℂ) = 0 := by
    simp only [mellin]
    refine (setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_).trans (integral_zero _ _)
    have hy : (0 : ℝ) < y := hy
    simp only [hW y hy, smul_zero]

  have hR : (RealArchParam.principal u₁ a₁ u₂ a₂).archFactor (σ : ℂ) ≠ 0 := by
    simp only [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC, Multiset.map_zero,
      Multiset.prod_zero, mul_one, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h₁) (Complex.Gammaℝ_ne_zero_of_re_pos h₂)
  exact hR (hL ▸ hid).symm

end S_LanglandsTunnell_principal_profile_exists_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_principal_profile_exists_ne_zero (solution)
