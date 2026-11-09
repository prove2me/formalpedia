-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weight16_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:49:57.834185+00:00
-- url     : https://prove2.me/submissions/1df2f9c4-1d2d-4978-911b-0642966e632e

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G086
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightBoxCalc_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
lemma weight16_contains_g_oai : weight16.Contains (fejerWeight 16) := by
  have he : weightBoxCalc 16 = weight16 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 16
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weight16_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weight16_contains_g_oai
