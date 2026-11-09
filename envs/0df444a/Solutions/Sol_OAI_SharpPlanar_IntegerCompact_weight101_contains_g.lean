-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weight101_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:49:26.04419+00:00
-- url     : https://prove2.me/submissions/25a87760-0f44-4a35-8b1f-1a6394ed200a

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
lemma weight101_contains_g_oai : weight101.Contains (fejerWeight 101) := by
  have he : weightBoxCalc 101 = weight101 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 101
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weight101_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weight101_contains_g_oai
