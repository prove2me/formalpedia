-- Prove2me | solution 1 for OAI.SharpPlanar.complexDirectFactor_disk_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:14:55.78064+00:00
-- url     : https://prove2.me/submissions/c137af7a-ac21-4e65-bd12-a56353da8671

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_disk_coordinate_bounds_g
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

lemma complexDirectFactor_disk_bound_g_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) {m y : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖complexDirectFactor m y ell t‖ ≤ Real.exp (Real.pi*(100/6+13/8)) := by
  have htn := (disk_coordinate_bounds_g hj ht).1
  have hti := (disk_coordinate_bounds_g hj ht).2.1
  have he : ‖Complex.exp (Complex.I*Real.pi*t*m)‖ ≤ Real.exp (Real.pi*100/6) := by
    refine (phase_exp_norm_bound_g hm0 hti).trans ?_
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hp : ‖(Complex.I*Real.pi*t*y)^ell/(ell.factorial:ℂ)‖ ≤
      Real.exp (Real.pi*(13/8)) := by
    refine (divided_power_norm_g _ ell).trans (Real.exp_le_exp.mpr ?_)
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hh := mul_le_mul htn hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 13/12)
    nlinarith [Real.pi_pos]
  rw [complexDirectFactor,mul_div_assoc,norm_mul]
  calc
    _ ≤ Real.exp (Real.pi*100/6)*Real.exp (Real.pi*(13/8)) :=
      mul_le_mul he hp (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexDirectFactor_disk_bound_g_oai := @OAI.SharpPlanar.complexDirectFactor_disk_bound_g_oai
