-- Prove2me | solution 1 for OAI.SharpPlanar.complexLambda_ofReal_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:13:09.740376+00:00
-- url     : https://prove2.me/submissions/09d86a5b-2e0b-485b-b3d3-7319dab69a4f

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

lemma complexLambda_ofReal_g_oai (t : ℝ) : complexLambda t = lambda t := rfl


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexLambda_ofReal_g_oai := @OAI.SharpPlanar.complexLambda_ofReal_g_oai
