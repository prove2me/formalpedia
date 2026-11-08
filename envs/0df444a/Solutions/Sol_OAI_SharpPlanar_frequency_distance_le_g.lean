-- Prove2me | solution 1 for OAI.SharpPlanar.frequency_distance_le_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:16.700435+00:00
-- url     : https://prove2.me/submissions/74d570de-1dd4-4e3e-b63b-36891f5019d8

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

lemma frequency_distance_le_g_oai {l : ℕ} (hl : l ≤ 6) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(l : ℂ)/6 - (t : ℂ)‖ ≤ 1 := by
  have he : (l : ℂ)/6 - (t : ℂ) = (((l : ℝ)/6 - t : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hln : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hlu : (l : ℝ) ≤ 6 := by exact_mod_cast hl
  constructor <;> linarith [ht.1, ht.2]


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.frequency_distance_le_g_oai := @OAI.SharpPlanar.frequency_distance_le_g_oai
