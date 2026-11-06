-- Prove2me | solution 1 for OAI.SharpPlanar.complexV_disk_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:33:52.768756+00:00
-- url     : https://prove2.me/submissions/a3bb95f3-92b1-4000-8ef4-e4076da57a86

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_atom_phase_norm_e
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


lemma complexV_disk_bound_e_oai {j n : ℕ} (hj : j < 6) (hn : n ≤ 100) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖complexV n j t‖ ≤ 250*Real.exp (100*Real.pi/6) := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ := norm_sum_le _ _
      _ = ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by simp only [norm_mul,atom_phase_norm_e,mul_one]
      _ ≤ 10 := positive_coeff_mass_le_e j
  unfold complexV
  simp only [norm_mul,Complex.norm_I,Complex.norm_ofNat,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ 2*Real.pi*Real.exp (100*Real.pi/6)*10 := by
      gcongr
      exact disk_phase_bound_e hj hn ht
    _ ≤ _ := by
      have := Real.pi_lt_d2
      have := Real.exp_pos (100*Real.pi/6)
      nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexV_disk_bound_e_oai := @OAI.SharpPlanar.complexV_disk_bound_e_oai
