-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.spectralCoefficient_eq_phase_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:09:34.163867+00:00
-- url     : https://prove2.me/submissions/d1f6d01a-9d91-4c86-8386-3f2f08c884a1

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

lemma spectralCoefficient_eq_phase_g_oai (n l : ℕ) :
    spectralCoefficient n l = Pcoeff l*phase12 (l*n) := by
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.spectralCoefficient_eq_phase_g_oai := @OAI.SharpPlanar.IntegerBasis.spectralCoefficient_eq_phase_g_oai
