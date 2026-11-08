-- Prove2me | solution 1 for OAI.SharpPlanar.lambda_sq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:30:30.457892+00:00
-- url     : https://prove2.me/submissions/89f934e0-7f37-44fe-a4a8-0102d4739013

import Mathlib
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_b_sq_g

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
lemma lambda_sq_g_oai (t : ℝ) : ‖lambda t‖^2 = (4/3:ℝ)/(t^2+h^2) := by
  rw [lambda,norm_div,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos b_pos_g,div_pow,mul_pow,kernel_den_sq,b_sq_g]
  field_simp

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.lambda_sq_g_oai := @OAI.SharpPlanar.lambda_sq_g_oai
