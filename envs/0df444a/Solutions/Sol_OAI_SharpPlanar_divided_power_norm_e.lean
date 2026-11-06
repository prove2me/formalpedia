-- Prove2me | solution 1 for OAI.SharpPlanar.divided_power_norm_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:07:51.189923+00:00
-- url     : https://prove2.me/submissions/88cff153-7e51-4e6a-8427-c5a394182360

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
open Complex

lemma divided_power_norm_e_oai (w : ℂ) (ell : ℕ) :
    ‖w^ell / (ell.factorial:ℂ)‖ ≤ Real.exp ‖w‖ := by
  simpa only [norm_div,norm_pow,Complex.norm_natCast] using
    Real.pow_div_factorial_le_exp ‖w‖ (norm_nonneg w) ell

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.divided_power_norm_e_oai := @OAI.SharpPlanar.divided_power_norm_e_oai
