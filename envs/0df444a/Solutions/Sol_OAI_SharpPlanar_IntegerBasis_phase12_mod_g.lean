-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.phase12_mod_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:04:02.379537+00:00
-- url     : https://prove2.me/submissions/467c9fc2-97c6-405f-9820-3561d3b8f071

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phase12_periodic_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phase12_mod_g_oai (n : ℕ) : phase12 (n%12) = phase12 n :=
  (show Function.Periodic phase12 12 from phase12_periodic_g).map_mod_nat n

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.phase12_mod_g_oai := @OAI.SharpPlanar.IntegerBasis.phase12_mod_g_oai
