-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.unit_phase_norm_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:06:20.731733+00:00
-- url     : https://prove2.me/submissions/e674fc83-adb0-47a7-afeb-4ead807748c5

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis

lemma unit_phase_norm_e_oai (n : ℕ) (t : ℝ) : ‖Complex.exp (-Complex.I*Real.pi*t*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.unit_phase_norm_e_oai := @OAI.SharpPlanar.IntegerBasis.unit_phase_norm_e_oai
