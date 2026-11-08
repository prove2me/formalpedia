-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.basisBeta_mod_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:06:56.84211+00:00
-- url     : https://prove2.me/submissions/dc88c580-9e8a-4714-bcbe-590881d67198

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

lemma basisBeta_mod_g_oai (n j : ℕ) : basisBeta (n%12) j = basisBeta n j := by
  unfold basisBeta
  simp only [spectralCoefficient_mod_g]

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.basisBeta_mod_g_oai := @OAI.SharpPlanar.IntegerBasis.basisBeta_mod_g_oai
