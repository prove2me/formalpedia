-- Prove2me | solution 1 for LanglandsTunnell.Converse.integral_ofReal_sq_mul_exp_neg_pi_mul_sq_div_sq_mul_psi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/805bdd51-9e9e-5fde-8cd4-b17ca3185fcb

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib
import Theorems.Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_integral_ofReal_sq_mul_exp_neg_pi_mul_sq_div_sq_mul_psi

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace Ws25Kit2
open LanglandsTunnell.Converse.ArchR Set MeasureTheory

theorem hasDerivAt_Gc (η : ℝ) :
    HasDerivAt (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) (-(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) η := by
  have h1 : HasDerivAt (fun y : ℝ => -(Real.pi * y ^ 2)) (-(Real.pi * (2 * η))) η := by
    have h__af := ((hasDerivAt_pow 2 η).const_mul Real.pi).fun_neg
    simp [pow_one] at h__af
    exact h__af
  have h3 : HasDerivAt (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ))
      (((Real.exp (-(Real.pi * η ^ 2)) * -(Real.pi * (2 * η)) : ℝ) : ℂ)) η :=
    ((Real.hasDerivAt_exp _).comp η h1).ofReal_comp
  convert h3 using 1; push_cast; ring

theorem deriv_Gc : deriv (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) =
    fun η => -(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := by
  funext η; exact (hasDerivAt_Gc η).deriv

theorem deriv2_Gc (η : ℝ) : deriv (deriv (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ))) η =
    ((2 * Real.pi) * (2 * Real.pi * η ^ 2 - 1) : ℝ) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := by
  rw [deriv_Gc]
  have hlin : HasDerivAt (fun η : ℝ => (-(2 * Real.pi * η) : ℂ)) (-(2 * Real.pi) : ℂ) η := by
    have : HasDerivAt (fun η : ℝ => -(2 * Real.pi * η)) (-(2 * Real.pi)) η := by
      have h__af := ((hasDerivAt_id η).const_mul (2 * Real.pi)).neg
      simp at h__af
      exact h__af
    convert this.ofReal_comp using 1 <;> push_cast <;> rfl
  have h := hlin.mul (hasDerivAt_Gc η)
  have h' : HasDerivAt (fun η : ℝ => -(2 * ↑Real.pi * (η : ℂ)) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ))
      ((-(2 * Real.pi) : ℂ) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) + (-(2 * Real.pi * (η : ℂ))) * (-(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ))) η := by
    convert h using 2
    rfl
    rfl
  rw [show (fun η : ℝ => -(2 * (Real.pi : ℂ) * (η : ℂ)) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) =
      fun η : ℝ => -(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) from by funext η; push_cast; ring] at h'
  rw [h'.deriv]; push_cast; ring

theorem moment_two (ξ : ℝ) :
    ∫ u : ℝ, ((u : ℝ) : ℂ) ^ 2 * (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      (((1 / (2 * Real.pi) - ξ ^ 2 : ℝ)) : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  rw [LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 2 ξ, iteratedDeriv_succ, iteratedDeriv_one,
    deriv2_Gc]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem x_moment2 (c : ℝ) {Y : ℝ} (hY : Y ≠ 0) :
    ∫ x : ℝ, ((x : ℝ) : ℂ) ^ 2 * (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * psi (c * x) =
      ((|Y| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * Y ^ 2))) : ℂ) * (((Y ^ 2 * (1 / (2 * Real.pi) - c ^ 2 * Y ^ 2) : ℝ)) : ℂ) := by
  have hy : 0 < |Y| := abs_pos.2 hY
  set ξ : ℝ := c * |Y| with hξ
  set f : ℝ → ℂ := fun x => ((x : ℝ) : ℂ) ^ 2 * (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * psi (c * x) with hf
  have hpt : ∀ u : ℝ, f (|Y| * u) =
      (((|Y| : ℝ) : ℂ) ^ 2) * (((u : ℝ) : ℂ) ^ 2 * (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) := by
    intro u
    have hsq : (|Y| * u) ^ 2 / Y ^ 2 = u ^ 2 := by rw [mul_pow, sq_abs]; field_simp
    have hpsi : psi (c * (|Y| * u)) = Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) := by
      rw [psi, hξ]; congr 1; push_cast; ring
    simp only [hf, hsq, hpsi]; push_cast; ring
  have hsub := Measure.integral_comp_mul_left f |Y|
  rw [abs_inv, abs_abs, Complex.real_smul] at hsub
  have hL : ∫ x, f x = ((|Y| : ℝ) : ℂ) * ∫ u : ℝ, f (|Y| * u) := by
    rw [hsub, ← mul_assoc, show ((|Y| : ℝ) : ℂ) * ((|Y|⁻¹ : ℝ) : ℂ) = 1 by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hy.ne', Complex.ofReal_one], one_mul]
  show ∫ x, f x = _
  rw [hL]; simp_rw [hpt]
  rw [integral_const_mul, moment_two, hξ, mul_pow, sq_abs]
  push_cast
  rw [show ((|Y| : ℝ) : ℂ) ^ 2 = (Y : ℂ) ^ 2 by rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]]
  ring

end Ws25Kit2

open LanglandsTunnell.Converse.ArchR in
theorem solution (c : ℝ) {Y : ℝ} (hY : Y ≠ 0) :
    ∫ x : ℝ, ((x : ℝ) : ℂ) ^ 2 * (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * ArchR.psi (c * x) =
      ((|Y| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * Y ^ 2))) : ℂ) * (((Y ^ 2 * (1 / (2 * Real.pi) - c ^ 2 * Y ^ 2) : ℝ)) : ℂ) := by
  exact Ws25Kit2.x_moment2 c hY

end S_LanglandsTunnell_Converse_integral_ofReal_sq_mul_exp_neg_pi_mul_sq_div_sq_mul_psi
end P2MW
export P2MW.S_LanglandsTunnell_Converse_integral_ofReal_sq_mul_exp_neg_pi_mul_sq_div_sq_mul_psi (solution)
