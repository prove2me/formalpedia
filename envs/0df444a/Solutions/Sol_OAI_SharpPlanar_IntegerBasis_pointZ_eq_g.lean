-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.pointZ_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:07:12.179521+00:00
-- url     : https://prove2.me/submissions/a2e2f618-655a-4f18-94c9-36c4d5d8dbcb

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

lemma pointZ_eq_g_oai (t : ℝ) : pointZ t = z t := by
  unfold pointZ z B h
  push_cast
  rfl

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.pointZ_eq_g_oai := @OAI.SharpPlanar.IntegerBasis.pointZ_eq_g_oai
