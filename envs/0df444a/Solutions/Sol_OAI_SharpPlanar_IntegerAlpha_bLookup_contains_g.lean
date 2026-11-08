-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bLookup_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:03:05.331784+00:00
-- url     : https://prove2.me/submissions/5ce2e0a6-b61e-4d24-8ada-983816a29796
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bTable_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisBeta_mod_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bLookup_contains_g_oai (n : ℕ) (j : Fin 6) : (bLookup n j).Contains (basisBeta n j.val) := by
  simpa only [bLookup,basisBeta_mod_g] using bTable_contains_g ⟨n%12,by omega⟩ j
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bLookup_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bLookup_contains_g_oai
