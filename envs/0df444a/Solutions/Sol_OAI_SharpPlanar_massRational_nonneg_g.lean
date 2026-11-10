-- Prove2me | solution 1 for OAI.SharpPlanar.massRational_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:25:09.370886+00:00
-- url     : https://prove2.me/submissions/9b5c00b2-3e59-4f82-aebf-314d4b501ab4

import Mathlib
import Definitions.Def_OAIQ098G362
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
lemma massRational_nonneg_g_oai (j : Fin 6) (n : ℕ) : 0 ≤ massRational j n := by
  have hs := slopeCap_nonneg_g j
  unfold massRational
  split_ifs <;> positivity
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.massRational_nonneg_g_oai := @OAI.SharpPlanar.massRational_nonneg_g_oai
