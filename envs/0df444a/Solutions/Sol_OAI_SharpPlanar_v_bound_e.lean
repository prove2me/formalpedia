-- Prove2me | solution 1 for OAI.SharpPlanar.v_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:22:06.835127+00:00
-- url     : https://prove2.me/submissions/f46f2c66-4f87-4684-a359-b52aea387473

import Mathlib
import Definitions.Def_OAIQ098E001
import Theorems.Thm_OAI_SharpPlanar_atom_phase_norm_e
import Theorems.Thm_OAI_SharpPlanar_positive_coeff_mass_le_e

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

lemma v_bound_e_oai (n j : ℕ) {t : ℝ} (_ : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ 20 * Real.pi := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ := norm_sum_le _ _
      _ = ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by simp only [norm_mul, atom_phase_norm_e, mul_one]
      _ ≤ 10 := positive_coeff_mass_le_e j
  unfold v
  rw [norm_mul, norm_mul, norm_mul, norm_mul, phase_norm]
  simp only [Complex.norm_ofNat, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]
  nlinarith [Real.pi_pos]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.v_bound_e_oai := @OAI.SharpPlanar.v_bound_e_oai
