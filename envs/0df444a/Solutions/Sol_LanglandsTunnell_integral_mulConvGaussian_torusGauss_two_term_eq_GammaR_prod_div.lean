-- Prove2me | solution 1 for LanglandsTunnell.integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/132f1e6a-33dd-52fd-89ea-c73718b1bbea

import Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow
import Theorems.Thm_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Real Complex MeasureTheory Set

namespace P2mKcK8TwoTerm

theorem bookkeeping (π₁ π₂ q₁ q₂ α β γ : ℂ)
    (hbal : β - γ = 2 * α + 2 + π₁ + π₂) (hq₂ : 0 < ((q₂ - γ - 1) / 2).re) :
    (1 / 2 * Gammaℝ (α - β + π₂) * Gammaℝ (q₂ - γ - 1) * Gammaℝ (α + 1 + π₁ + q₁) / (Real.pi : ℂ)) *
      (Complex.Gamma ((α - β + π₁ + 1) / 2) * Complex.Gamma ((α + 2 + π₂ + q₂) / 2) *
        Complex.Gamma ((α + 2 + π₂ + q₁) / 2) * Complex.Gamma ((α + 1 + π₁ + q₂) / 2) /
        (Complex.Gamma ((q₂ - γ - 1) / 2) * Complex.Gamma ((β - γ + q₁ + q₂ + 1) / 2)))
      = 1 / 2 * (Gammaℝ (α - β + π₁ + 1) * Gammaℝ (α - β + π₂) *
          (Gammaℝ (α + 1 + π₁ + q₁) * Gammaℝ (α + 1 + π₁ + q₂) *
            Gammaℝ (α + 2 + π₂ + q₁) * Gammaℝ (α + 2 + π₂ + q₂))) / Gammaℝ (β - γ + q₁ + q₂ + 1) := by
  simp only [Gammaℝ_def]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_pos.ne'
  have hΓq : Complex.Gamma ((q₂ - γ - 1) / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hq₂
  have kπ : (Real.pi : ℂ) ^ (-(q₂ - γ - 1) / 2) / (Real.pi : ℂ)
      = (Real.pi : ℂ) ^ (-(α - β + π₁ + 1) / 2) * (Real.pi : ℂ) ^ (-(α + 1 + π₁ + q₂) / 2) *
          (Real.pi : ℂ) ^ (-(α + 2 + π₂ + q₁) / 2) * (Real.pi : ℂ) ^ (-(α + 2 + π₂ + q₂) / 2) /
          (Real.pi : ℂ) ^ (-(β - γ + q₁ + q₂ + 1) / 2) := by
    rw [show (Real.pi : ℂ) ^ (-(q₂ - γ - 1) / 2) / (Real.pi : ℂ) = (Real.pi : ℂ) ^ (-(q₂ - γ - 1) / 2 - 1) by
        rw [cpow_sub _ _ hπ, cpow_one], ← cpow_add _ _ hπ, ← cpow_add _ _ hπ, ← cpow_add _ _ hπ, ← cpow_sub _ _ hπ]
    congr 1
    linear_combination (-1 : ℂ) * hbal
  calc _ = 1 / 2 * (Real.pi : ℂ) ^ (-(α - β + π₂) / 2) * (Real.pi : ℂ) ^ (-(α + 1 + π₁ + q₁) / 2) *
        Complex.Gamma ((α - β + π₂) / 2) * Complex.Gamma ((α + 1 + π₁ + q₁) / 2) *
        (Complex.Gamma ((α - β + π₁ + 1) / 2) * Complex.Gamma ((α + 2 + π₂ + q₂) / 2) *
          Complex.Gamma ((α + 2 + π₂ + q₁) / 2) * Complex.Gamma ((α + 1 + π₁ + q₂) / 2)) *
        ((Real.pi : ℂ) ^ (-(q₂ - γ - 1) / 2) / (Real.pi : ℂ) / Complex.Gamma ((β - γ + q₁ + q₂ + 1) / 2)) *
        (Complex.Gamma ((q₂ - γ - 1) / 2) / Complex.Gamma ((q₂ - γ - 1) / 2)) := by ring
    _ = 1 / 2 * (Real.pi : ℂ) ^ (-(α - β + π₂) / 2) * (Real.pi : ℂ) ^ (-(α + 1 + π₁ + q₁) / 2) *
        Complex.Gamma ((α - β + π₂) / 2) * Complex.Gamma ((α + 1 + π₁ + q₁) / 2) *
        (Complex.Gamma ((α - β + π₁ + 1) / 2) * Complex.Gamma ((α + 2 + π₂ + q₂) / 2) *
          Complex.Gamma ((α + 2 + π₂ + q₁) / 2) * Complex.Gamma ((α + 1 + π₁ + q₂) / 2)) *
        (((Real.pi : ℂ) ^ (-(α - β + π₁ + 1) / 2) * (Real.pi : ℂ) ^ (-(α + 1 + π₁ + q₂) / 2) *
          (Real.pi : ℂ) ^ (-(α + 2 + π₂ + q₁) / 2) * (Real.pi : ℂ) ^ (-(α + 2 + π₂ + q₂) / 2) /
          (Real.pi : ℂ) ^ (-(β - γ + q₁ + q₂ + 1) / 2)) / Complex.Gamma ((β - γ + q₁ + q₂ + 1) / 2)) * 1 := by
          rw [kπ, div_self hΓq]
    _ = _ := by ring

theorem main (π₁ π₂ q₁ q₂ α β γ : ℂ)
    (hbal : β - γ = 2 * α + 2 + π₁ + π₂)
    (hp₁ : 0 < (α - β + π₁ + 1).re) (hp₂ : 0 < (α - β + π₂).re)
    (h₁₁ : 0 < (α + 1 + π₁ + q₁).re) (h₁₂ : 0 < (α + 1 + π₁ + q₂).re)
    (h₂₁ : 0 < (α + 2 + π₂ + q₁).re) (h₂₂ : 0 < (α + 2 + π₂ + q₂).re) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (π₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (π₂ + 1) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (α) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (q₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (q₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (β - 1) * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) +
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (π₁ + 1) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (π₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (α + 1) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (q₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (q₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (β + 1) * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ))
      = (1 / 2 : ℂ) *
          (Complex.Gammaℝ (α - β + π₁ + 1) * Complex.Gammaℝ (α - β + π₂) *
            (Complex.Gammaℝ (α + 1 + π₁ + q₁) * Complex.Gammaℝ (α + 1 + π₁ + q₂) *
              Complex.Gammaℝ (α + 2 + π₂ + q₁) * Complex.Gammaℝ (α + 2 + π₂ + q₂))) /
          Complex.Gammaℝ (β - γ + q₁ + q₂ + 1) := by
  have hbalR : β.re - γ.re = 2 * α.re + 2 + π₁.re + π₂.re := by
    have := congrArg Complex.re hbal; simpa using this
  simp only [add_re, sub_re, one_re, re_ofNat] at hp₁ hp₂ h₁₁ h₁₂ h₂₁ h₂₂
  have ha_ne : α - β + π₂ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hd_ne : α + 1 + π₁ + q₁ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith

  have R1 := LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow
    π₁ (π₂ + 1) q₁ q₂ α (β - 1) γ (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have R2 := LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow
    (π₁ + 1) π₂ q₁ q₂ (α + 1) (β + 1) γ (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  rw [R1, R2]

  rw [show (α - (β - 1) + π₁) / 2 - 1 = (α - β + π₁ + 1) / 2 - 1 by ring,
    show -((α - (β - 1) + (π₂ + 1)) / 2) = -((α - β + π₂) / 2 + 1) by ring,
    show (q₁ - γ - 1) / 2 - 1 = (α - β + π₂) / 2 + (α + 1 + π₁ + q₁) / 2 - 1 by
      linear_combination (1 / 2 : ℂ) * hbal,
    show (α + 1 - (β + 1) + (π₁ + 1)) / 2 - 1 = (α - β + π₁ + 1) / 2 - 1 by ring,
    show -((α + 1 - (β + 1) + π₂) / 2) = -((α - β + π₂) / 2) by ring,
    show -((α + 1 + 1 + (π₁ + 1) + q₁) / 2) = -((α + 1 + π₁ + q₁) / 2 + 1) by ring]

  rw [show α - (β - 1) + (π₂ + 1) = (α - β + π₂) + 2 by ring, show α + 1 - (β + 1) + π₂ = α - β + π₂ by ring,
    show α + 1 + 1 + (π₁ + 1) + q₁ = (α + 1 + π₁ + q₁) + 2 by ring, Gammaℝ_add_two ha_ne, Gammaℝ_add_two hd_ne]

  have H2 := Complex.mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance
    ((α - β + π₁ + 1) / 2) ((α - β + π₂) / 2) ((q₂ - γ - 1) / 2) ((α + 1 + π₁ + q₁) / 2)
    (by rw [div_ofNat_re]; simp; linarith) (by rw [div_ofNat_re]; simp; linarith)
    (by rw [div_ofNat_re]; simp; linarith)
    (by rw [sub_re, div_ofNat_re, div_ofNat_re]; simp; linarith)
    (by rw [add_re, sub_re, div_ofNat_re, div_ofNat_re, one_re]; simp; linarith)
    (by rw [add_re, sub_re, add_re, div_ofNat_re, div_ofNat_re, div_ofNat_re, one_re]; simp; linarith)
  rw [show (q₂ - γ - 1) / 2 - (α - β + π₁ + 1) / 2 + 1 = (α + 2 + π₂ + q₂) / 2 by
      linear_combination (1 / 2 : ℂ) * hbal,
    show (α - β + π₂) / 2 + (α + 1 + π₁ + q₁) / 2 - (α - β + π₁ + 1) / 2 + 1 = (α + 2 + π₂ + q₁) / 2 by ring,
    show (q₂ - γ - 1) / 2 - (α - β + π₂) / 2 = (α + 1 + π₁ + q₂) / 2 by linear_combination (1 / 2 : ℂ) * hbal,
    show (α + 1 + π₁ + q₁) / 2 + (q₂ - γ - 1) / 2 - (α - β + π₁ + 1) / 2 + 1 = (β - γ + q₁ + q₂ + 1) / 2 by ring] at H2
  have hG := bookkeeping π₁ π₂ q₁ q₂ α β γ hbal (by rw [div_ofNat_re]; simp; linarith)
  linear_combination
    (1 / 2 * Gammaℝ (α - β + π₂) * Gammaℝ (q₂ - γ - 1) * Gammaℝ (α + 1 + π₁ + q₁) / (Real.pi : ℂ)) * H2 + hG

end P2mKcK8TwoTerm

end

theorem solution
    (π₁ π₂ q₁ q₂ α β γ : ℂ)
    (hbal : β - γ = 2 * α + 2 + π₁ + π₂)
    (hp₁ : 0 < (α - β + π₁ + 1).re) (hp₂ : 0 < (α - β + π₂).re)
    (h₁₁ : 0 < (α + 1 + π₁ + q₁).re) (h₁₂ : 0 < (α + 1 + π₁ + q₂).re)
    (h₂₁ : 0 < (α + 2 + π₂ + q₁).re) (h₂₂ : 0 < (α + 2 + π₂ + q₂).re) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (π₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (π₂ + 1) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (α) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (q₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (q₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (β - 1) * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) +
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (π₁ + 1) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (π₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (α + 1) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (q₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (q₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (β + 1) * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ))
      = (1 / 2 : ℂ) *
          (Complex.Gammaℝ (α - β + π₁ + 1) * Complex.Gammaℝ (α - β + π₂) *
            (Complex.Gammaℝ (α + 1 + π₁ + q₁) * Complex.Gammaℝ (α + 1 + π₁ + q₂) *
              Complex.Gammaℝ (α + 2 + π₂ + q₁) * Complex.Gammaℝ (α + 2 + π₂ + q₂))) /
          Complex.Gammaℝ (β - γ + q₁ + q₂ + 1) :=
  P2mKcK8TwoTerm.main π₁ π₂ q₁ q₂ α β γ hbal hp₁ hp₂ h₁₁ h₁₂ h₂₁ h₂₂

end S_LanglandsTunnell_integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div
end P2MW
export P2MW.S_LanglandsTunnell_integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div (solution)
