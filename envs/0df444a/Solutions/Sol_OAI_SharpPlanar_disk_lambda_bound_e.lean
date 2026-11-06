-- Prove2me | solution 1 for OAI.SharpPlanar.disk_lambda_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:37:34.873221+00:00
-- url     : https://prove2.me/submissions/513df102-4b45-4ed4-86a2-3df7746308ea

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_b_pos_e
import Theorems.Thm_OAI_SharpPlanar_b_sq_e
import Theorems.Thm_OAI_SharpPlanar_disk_denominator_lower_e

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

lemma b_lower_simple : 43/50 < b := by
  have hh := b_sq_e
  have hp := b_pos_e
  nlinarith

lemma disk_lambda_bound_e_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖complexLambda t‖ < 5 := by
  have hd := disk_denominator_lower_e hj ht
  have hb := b_lower_simple
  rw [complexLambda,norm_div,norm_mul,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos b_pos_e]
  apply (div_lt_iff₀ (mul_pos b_pos_e (by linarith))).mpr
  nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_lambda_bound_e_oai := @OAI.SharpPlanar.disk_lambda_bound_e_oai
