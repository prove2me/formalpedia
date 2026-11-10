-- Prove2me | solution 1 for OAI.SharpPlanar.pieceMass_le_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:21:57.676359+00:00
-- url     : https://prove2.me/submissions/860f4404-8a63-430a-ae5e-ce1822522a22

import Mathlib
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_pi_fine_g
import Theorems.Thm_OAI_SharpPlanar_slopeCap_nonneg_g

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
lemma pieceMass_le_g_oai (j : Fin 6) (n : ℕ) : pieceMass j n ≤ massRational j n := by
  unfold pieceMass massRational
  split_ifs with hz
  · rfl
  · apply min_le_min_left
    have hpos : 0 < slopeCap j*(n:ℝ) := lt_of_le_of_ne (mul_nonneg (slopeCap_nonneg_g j) (Nat.cast_nonneg n)) (Ne.symm hz)
    apply one_div_le_one_div_of_le
    · nlinarith
    · nlinarith [pi_fine_g]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceMass_le_g_oai := @OAI.SharpPlanar.pieceMass_le_g_oai
