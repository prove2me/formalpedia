-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.pointZ_eq_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T15:03:20.541427+00:00
-- url     : https://prove2.me/submissions/2b6c9455-5545-4b02-9433-6973747f20c5

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

lemma pointZ_eq_e_oai (t : ℝ) : pointZ t = z t := by
  unfold pointZ z B h
  push_cast
  rfl

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.pointZ_eq_e_oai := @OAI.SharpPlanar.IntegerBasis.pointZ_eq_e_oai
