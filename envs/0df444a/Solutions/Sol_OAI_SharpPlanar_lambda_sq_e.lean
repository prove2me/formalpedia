-- Prove2me | solution 1 for OAI.SharpPlanar.lambda_sq_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:17:40.439623+00:00
-- url     : https://prove2.me/submissions/790bb04f-3440-4fab-8097-2a26839476d5

import Mathlib
import Definitions.Def_OAIQ098E001
import Theorems.Thm_OAI_SharpPlanar_b_pos_e
import Theorems.Thm_OAI_SharpPlanar_b_sq_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma kernel_den_sq (t : ℝ) : ‖(t:ℂ)+Complex.I*h‖^2 = t^2+h^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,pow_two]
lemma lambda_sq_e_oai (t : ℝ) : ‖lambda t‖^2 = (4/3:ℝ)/(t^2+h^2) := by
  rw [lambda,norm_div,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos b_pos_e,div_pow,mul_pow,kernel_den_sq,b_sq_e]
  field_simp

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.lambda_sq_e_oai := @OAI.SharpPlanar.lambda_sq_e_oai
