-- Prove2me | solution 1 for OAI.SharpPlanar.complexZ_ofReal_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:14:15.11567+00:00
-- url     : https://prove2.me/submissions/18d57511-b13b-4269-a07c-baaaaa4f946b

import Mathlib
import Definitions.Def_OAIQ098G072

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis

lemma complexZ_ofReal_g_oai (t : ℝ) : complexZ t = z t := rfl


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexZ_ofReal_g_oai := @OAI.SharpPlanar.complexZ_ofReal_g_oai
