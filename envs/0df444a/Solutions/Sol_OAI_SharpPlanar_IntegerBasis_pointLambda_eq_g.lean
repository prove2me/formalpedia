-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.pointLambda_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:05:56.551019+00:00
-- url     : https://prove2.me/submissions/d25a6dd4-a5d1-4237-a109-02209204e01f

import Mathlib
import Definitions.Def_OAIQ098G072

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma pointLambda_eq_g_oai (t : ℝ) : pointLambda t = lambda t := by
  unfold pointLambda lambda b h
  push_cast
  rfl

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.pointLambda_eq_g_oai := @OAI.SharpPlanar.IntegerBasis.pointLambda_eq_g_oai
