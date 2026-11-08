-- Prove2me | solution 1 for OAI.SharpPlanar.complexTransformedFactor_disk_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:18:13.309371+00:00
-- url     : https://prove2.me/submissions/2b3051bd-8d6c-4b15-b900-021badc96bc7

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_disk_lambda_bound_g
import Theorems.Thm_OAI_SharpPlanar_disk_z_bound_g
import Theorems.Thm_OAI_SharpPlanar_disk_z_imaginary_simple_g
import Theorems.Thm_OAI_SharpPlanar_divided_power_norm_g
import Theorems.Thm_OAI_SharpPlanar_phase_exp_norm_bound_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open Complex

lemma complexTransformedFactor_disk_bound_g_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) {m y : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖complexTransformedFactor m y ell t‖ ≤ 5*Real.exp (Real.pi*(87/5)) := by
  have htn := (disk_z_bound_g hj ht).le
  have hti := (disk_z_imaginary_simple_g hj ht).le
  have he : ‖Complex.exp (Complex.I*Real.pi*complexZ t*m)‖ ≤ Real.exp (Real.pi*(81/10)) := by
    refine (phase_exp_norm_bound_g hm0 hti).trans ?_
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hp : ‖(Complex.I*Real.pi*complexZ t*y)^ell/(ell.factorial:ℂ)‖ ≤
      Real.exp (Real.pi*(93/10)) := by
    refine (divided_power_norm_g _ ell).trans (Real.exp_le_exp.mpr ?_)
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hh := mul_le_mul htn hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 31/5)
    nlinarith [Real.pi_pos]
  rw [complexTransformedFactor,mul_div_assoc,norm_mul,norm_mul]
  calc
    _ ≤ (5*Real.exp (Real.pi*(81/10)))*Real.exp (Real.pi*(93/10)) :=
      mul_le_mul (mul_le_mul (disk_lambda_bound_g hj ht).le he (norm_nonneg _)
        (by norm_num)) hp (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexTransformedFactor_disk_bound_g_oai := @OAI.SharpPlanar.complexTransformedFactor_disk_bound_g_oai
