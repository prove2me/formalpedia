-- Prove2me | solution 1 for OAI.SharpPlanar.atom_phase_norm_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:07:04.810198+00:00
-- url     : https://prove2.me/submissions/666c72ce-2ef0-4808-b821-4929f97d7ed9

import Mathlib

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

lemma atom_phase_norm_e_oai (n l : ℕ) :
    ‖Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)‖ = 1 := by
  simp [Complex.norm_exp]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.atom_phase_norm_e_oai := @OAI.SharpPlanar.atom_phase_norm_e_oai
