-- Prove2me | solution 1 for LanglandsTunnell.ArchBessel.besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5bdf623f-0977-56d1-b6ae-d82c3a7092eb

import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div

set_option autoImplicit false

open MeasureTheory Set LanglandsTunnell.ArchBessel

theorem solution
    (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    besselKernel ν x =
      (((2 / x : ℝ)) : ℂ) ^ ν *
        ∫ τ in Set.Ioi (0 : ℝ), (Real.exp (-(τ + x ^ 2 / (4 * τ))) : ℂ) * ((τ : ℂ) ^ (ν - 1)) := by
  have hx2 : 0 < x / 2 := by positivity
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hx20 : (((x / 2 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx2.ne'
  set g : ℝ → ℂ := fun τ => (Real.exp (-(τ + x ^ 2 / (4 * τ))) : ℂ) * ((τ : ℂ) ^ (ν - 1)) with hg

  have hsub := integral_comp_mul_left_Ioi g 0 hx2
  rw [mul_zero] at hsub

  have hpt : ∀ t : ℝ, 0 < t → g (x / 2 * t) =
      (((x / 2 : ℝ)) : ℂ) ^ (ν - 1) * ((Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))) := by
    intro t ht
    simp only [hg]
    have e1 : -(x / 2 * t + x ^ 2 / (4 * (x / 2 * t))) = -(x * (t + t⁻¹) / 2) := by
      field_simp
      ring
    have e2 : (((x / 2 * t : ℝ)) : ℂ) ^ (ν - 1) = (((x / 2 : ℝ)) : ℂ) ^ (ν - 1) * (t : ℂ) ^ (ν - 1) := by
      rw [Complex.ofReal_mul]
      exact Complex.mul_cpow_ofReal_nonneg hx2.le ht.le (ν - 1)
    rw [e1, e2]; ring
  have hI : ∫ t in Ioi (0 : ℝ), g (x / 2 * t) =
      (((x / 2 : ℝ)) : ℂ) ^ (ν - 1) * besselKernel ν x := by
    unfold besselKernel
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpt t ht)

  have hJ : ∫ τ in Ioi (0 : ℝ), g τ = (x / 2 : ℝ) • ((((x / 2 : ℝ)) : ℂ) ^ (ν - 1) * besselKernel ν x) := by
    rw [← hI, hsub, smul_smul, mul_inv_cancel₀ hx2.ne', one_smul]
  show besselKernel ν x = (((2 / x : ℝ)) : ℂ) ^ ν * ∫ τ in Ioi (0 : ℝ), g τ
  rw [hJ, Complex.real_smul]
  have e3 : (((x / 2 : ℝ)) : ℂ) * (((x / 2 : ℝ)) : ℂ) ^ (ν - 1) = (((x / 2 : ℝ)) : ℂ) ^ ν := by
    rw [show (((x / 2 : ℝ)) : ℂ) * (((x / 2 : ℝ)) : ℂ) ^ (ν - 1) =
        (((x / 2 : ℝ)) : ℂ) ^ (1 : ℂ) * (((x / 2 : ℝ)) : ℂ) ^ (ν - 1) by rw [Complex.cpow_one],
      ← Complex.cpow_add _ _ hx20]
    congr 1; ring
  have e4 : (((2 / x : ℝ)) : ℂ) ^ ν * (((x / 2 : ℝ)) : ℂ) ^ ν = 1 := by
    rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) hx2.le]
    have : (((2 / x : ℝ)) : ℂ) * (((x / 2 : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]; rw [show (2 / x) * (x / 2) = (1 : ℝ) by field_simp]; simp
    rw [this, Complex.one_cpow]
  calc besselKernel ν x = 1 * besselKernel ν x := (one_mul _).symm
    _ = ((((2 / x : ℝ)) : ℂ) ^ ν * ((((x / 2 : ℝ)) : ℂ) * (((x / 2 : ℝ)) : ℂ) ^ (ν - 1))) * besselKernel ν x := by
        rw [e3, e4]
    _ = (((2 / x : ℝ)) : ℂ) ^ ν * ((((x / 2 : ℝ)) : ℂ) * ((((x / 2 : ℝ)) : ℂ) ^ (ν - 1) * besselKernel ν x)) := by
        ring

#print axioms solution

end S_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div
end P2MW
export P2MW.S_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div (solution)
