-- Prove2me | solution 1 for OAI.SharpPlanar.pieceMass_le_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:22:05.825221+00:00
-- url     : https://prove2.me/submissions/c7a1d3a0-c4fa-4a61-801e-dae7c167010e

import Mathlib
import Definitions.Def_OAIQ098E125
import Theorems.Thm_OAI_SharpPlanar_pi_fine_e
import Theorems.Thm_OAI_SharpPlanar_slopeCap_nonneg_e

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
open IntegerBasis
lemma pieceMass_le_e_oai (j : Fin 6) (n : ℕ) : pieceMass j n ≤ massRational j n := by
  unfold pieceMass massRational
  split_ifs with hz
  · rfl
  · apply min_le_min_left
    have hpos : 0 < slopeCap j*(n:ℝ) := lt_of_le_of_ne (mul_nonneg (slopeCap_nonneg_e j) (Nat.cast_nonneg n)) (Ne.symm hz)
    apply one_div_le_one_div_of_le
    · nlinarith
    · nlinarith [pi_fine_e]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceMass_le_e_oai := @OAI.SharpPlanar.pieceMass_le_e_oai
