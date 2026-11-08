-- Prove2me | solution 1 for OAI.SharpPlanar.piece_interval_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:54.573359+00:00
-- url     : https://prove2.me/submissions/75503f82-bd54-43f5-b42f-7dada199f5cb

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

lemma piece_interval_g_oai {j : ℕ} (hj : j < 6) {t : ℝ}
    (ht : t ∈ Set.uIcc ((j : ℝ)/6) (((j : ℝ)+1)/6)) : t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.uIcc_of_le (by linarith : (j : ℝ)/6 ≤ ((j : ℝ)+1)/6)] at ht
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj5 : (j : ℝ) ≤ 5 := by exact_mod_cast (show j ≤ 5 by omega)
  constructor <;> linarith [ht.1, ht.2]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.piece_interval_g_oai := @OAI.SharpPlanar.piece_interval_g_oai
