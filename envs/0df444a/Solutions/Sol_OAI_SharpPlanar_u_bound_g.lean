-- Prove2me | solution 1 for OAI.SharpPlanar.u_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:48:11.887206+00:00
-- url     : https://prove2.me/submissions/89b0c33d-616d-41f8-8519-a6e08a42a44c

import Mathlib
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_atom_phase_norm_g
import Theorems.Thm_OAI_SharpPlanar_frequency_distance_le_g
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


lemma u_bound_g_oai (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖u n j t‖ ≤ 20 * Real.pi^2 := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      ((l : ℂ)/6-t) * Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖((l : ℂ)/6-t) * Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by
        apply Finset.sum_le_sum
        intro l hl
        rw [norm_mul, norm_mul, atom_phase_norm_g, mul_one]
        exact (mul_le_mul_of_nonneg_right (frequency_distance_le_g (Finset.mem_Icc.mp hl).2 ht)
          (norm_nonneg _)).trans_eq (one_mul _)
      _ ≤ 10 := positive_coeff_mass_le_g j
  unfold u
  rw [norm_mul, norm_mul, norm_mul, norm_pow, phase_norm]
  simp only [norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]
  nlinarith [sq_nonneg Real.pi]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.u_bound_g_oai := @OAI.SharpPlanar.u_bound_g_oai
