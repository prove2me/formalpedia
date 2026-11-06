-- Prove2me | solution 1 for OAI.SharpPlanar.complexU_disk_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:33:51.760607+00:00
-- url     : https://prove2.me/submissions/eeb9a6e3-d4cd-4e3a-b4db-00d5fe52dd6f

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_atom_phase_norm_e
import Theorems.Thm_OAI_SharpPlanar_disk_frequency_distance_e
import Theorems.Thm_OAI_SharpPlanar_disk_phase_bound_e
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
open MeasureTheory Set


lemma complexU_disk_bound_e_oai {j n : ℕ} (hj : j < 6) (hn : n ≤ 100) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖complexU n j t‖ ≤ 250*Real.exp (100*Real.pi/6) := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      ((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ ≤ (13/12)*10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6, (13/12)*‖Pcoeff l‖ := by
        apply Finset.sum_le_sum
        intro l hl
        rw [norm_mul,norm_mul,atom_phase_norm_e,mul_one]
        exact mul_le_mul_of_nonneg_right (disk_frequency_distance_e hj hl ht) (norm_nonneg _)
      _ ≤ (13/12)*10 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (positive_coeff_mass_le_e j) (by norm_num)
  unfold complexU
  simp only [norm_mul,norm_pow,norm_neg,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ 2*Real.pi^2 * Real.exp (100*Real.pi/6) * ((13/12)*10) := by
      gcongr
      exact disk_phase_bound_e hj hn ht
    _ ≤ _ := by
      have hp := Real.pi_lt_d2
      have hp0 := Real.pi_pos
      have hp2 : Real.pi^2 < 10 := by nlinarith
      have he := Real.exp_pos (100*Real.pi/6)
      nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexU_disk_bound_e_oai := @OAI.SharpPlanar.complexU_disk_bound_e_oai
