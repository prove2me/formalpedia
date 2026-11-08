-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.basisAlpha_mod_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:06:43.397304+00:00
-- url     : https://prove2.me/submissions/f7fb9fa0-7ca3-4b24-83cb-f3472a13363c

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_spectralCoefficient_mod_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma basisAlpha_mod_g_oai (n j : ℕ) : basisAlpha (n%12) j = basisAlpha n j := by
  unfold basisAlpha
  simp only [spectralCoefficient_mod_g]

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.basisAlpha_mod_g_oai := @OAI.SharpPlanar.IntegerBasis.basisAlpha_mod_g_oai
