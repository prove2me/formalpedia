-- Prove2me | solution 1 for OAI.SharpPlanar.disk_phase_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:18:27.895191+00:00
-- url     : https://prove2.me/submissions/5d8011e9-012e-4594-b396-59b363eb79c3

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_disk_coordinate_bounds_g

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


lemma disk_phase_bound_g_oai {j n : ℕ} (hj : j < 6) (hn : n ≤ 100) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖Complex.exp (-Complex.I*Real.pi*t*n)‖ ≤ Real.exp (100*Real.pi/6) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have ht' := (disk_coordinate_bounds_g hj ht).2.2
  have hn' : (n:ℝ) ≤ 100 := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,zero_mul,
    mul_zero,sub_zero,neg_zero,Complex.mul_im,zero_add]
  nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le hn0,
    mul_nonneg Real.pi_pos.le (show 0 ≤ 100-(n:ℝ) by linarith)]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_phase_bound_g_oai := @OAI.SharpPlanar.disk_phase_bound_g_oai
