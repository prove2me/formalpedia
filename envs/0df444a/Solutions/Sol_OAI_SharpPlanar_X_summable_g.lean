-- Prove2me | solution 1 for OAI.SharpPlanar.X_summable_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:13:43.744538+00:00
-- url     : https://prove2.me/submissions/3a29051a-1ad6-486d-9a74-da31ef51760d

import Mathlib
import Definitions.Def_OAIQ098G001

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



theorem X_summable_g_oai (x : X) : Summable (fun ni : Node × Bool => |x ni|) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.X_summable_g_oai := @OAI.SharpPlanar.X_summable_g_oai
