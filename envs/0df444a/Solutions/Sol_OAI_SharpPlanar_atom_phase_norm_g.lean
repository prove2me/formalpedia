-- Prove2me | solution 1 for OAI.SharpPlanar.atom_phase_norm_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:05:39.028435+00:00
-- url     : https://prove2.me/submissions/1dd8f81a-8c98-4770-a521-7e8d837bf864

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

lemma atom_phase_norm_g_oai (n l : ℕ) :
    ‖Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)‖ = 1 := by
  simp [Complex.norm_exp]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.atom_phase_norm_g_oai := @OAI.SharpPlanar.atom_phase_norm_g_oai
