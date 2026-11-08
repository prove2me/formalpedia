-- Prove2me | solution 1 for OAI.SharpPlanar.divided_power_norm_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:05:55.10562+00:00
-- url     : https://prove2.me/submissions/ed6b1dae-06b3-4190-8dbb-7a851608c022

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

lemma divided_power_norm_g_oai (w : ℂ) (ell : ℕ) :
    ‖w^ell / (ell.factorial:ℂ)‖ ≤ Real.exp ‖w‖ := by
  simpa only [norm_div,norm_pow,Complex.norm_natCast] using
    Real.pow_div_factorial_le_exp ‖w‖ (norm_nonneg w) ell

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.divided_power_norm_g_oai := @OAI.SharpPlanar.divided_power_norm_g_oai
