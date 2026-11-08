-- Prove2me | solution 1 for OAI.SharpPlanar.v_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:49:40.2892+00:00
-- url     : https://prove2.me/submissions/fb14775e-9b2c-41a8-951a-e0b5d66ce748

import Mathlib
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_atom_phase_norm_g
import Theorems.Thm_OAI_SharpPlanar_positive_coeff_mass_le_g

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

lemma phase_norm (n : ℕ) (t : ℝ) :
    ‖Complex.exp (-Complex.I * Real.pi * t * n)‖ = 1 := by
  simp [Complex.norm_exp]

lemma v_bound_g_oai (n j : ℕ) {t : ℝ} (_ : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ 20 * Real.pi := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ := norm_sum_le _ _
      _ = ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by simp only [norm_mul, atom_phase_norm_g, mul_one]
      _ ≤ 10 := positive_coeff_mass_le_g j
  unfold v
  rw [norm_mul, norm_mul, norm_mul, norm_mul, phase_norm]
  simp only [Complex.norm_ofNat, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]
  nlinarith [Real.pi_pos]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.v_bound_g_oai := @OAI.SharpPlanar.v_bound_g_oai
