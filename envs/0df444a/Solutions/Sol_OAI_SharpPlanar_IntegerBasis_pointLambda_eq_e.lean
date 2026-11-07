-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.pointLambda_eq_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T15:03:19.559047+00:00
-- url     : https://prove2.me/submissions/3faa15b1-d430-42f3-8b49-9ec2cdc2fb71

import Mathlib
import Definitions.Def_OAIQ098E018

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma pointLambda_eq_e_oai (t : ℝ) : pointLambda t = lambda t := by
  unfold pointLambda lambda b h
  push_cast
  rfl

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.pointLambda_eq_e_oai := @OAI.SharpPlanar.IntegerBasis.pointLambda_eq_e_oai
