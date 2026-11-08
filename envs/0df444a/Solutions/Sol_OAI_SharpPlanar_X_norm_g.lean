-- Prove2me | solution 1 for OAI.SharpPlanar.X_norm_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:13:35.069853+00:00
-- url     : https://prove2.me/submissions/7f23791a-ea08-41be-a380-5f4c91410c58

import Mathlib
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_X_summable_g

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


theorem X_norm_g_oai (x : X) : ‖x‖ = ∑' n : Node, (|x (n, false)| + |x (n, true)|) := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one, Real.norm_eq_abs]
  rw [(X_summable_g x).tsum_prod]
  simp only [tsum_bool]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.X_norm_g_oai := @OAI.SharpPlanar.X_norm_g_oai
