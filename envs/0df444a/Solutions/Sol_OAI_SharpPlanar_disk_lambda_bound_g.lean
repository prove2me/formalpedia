-- Prove2me | solution 1 for OAI.SharpPlanar.disk_lambda_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:16:53.726986+00:00
-- url     : https://prove2.me/submissions/6ab9a84f-f504-4001-a705-5626a34dc384

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_b_sq_g
import Theorems.Thm_OAI_SharpPlanar_disk_denominator_lower_g

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
  have hh := b_sq_g
  have hp := b_pos_g
  nlinarith

lemma disk_lambda_bound_g_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖complexLambda t‖ < 5 := by
  have hd := disk_denominator_lower_g hj ht
  have hb := b_lower_simple
  rw [complexLambda,norm_div,norm_mul,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos b_pos_g]
  apply (div_lt_iff₀ (mul_pos b_pos_g (by linarith))).mpr
  nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_lambda_bound_g_oai := @OAI.SharpPlanar.disk_lambda_bound_g_oai
