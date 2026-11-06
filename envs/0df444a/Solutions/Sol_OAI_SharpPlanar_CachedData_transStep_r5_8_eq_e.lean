-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.transStep_r5_8_eq_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T01:34:36.081905+00:00
-- url     : https://prove2.me/submissions/a071aafb-4a8d-439d-b279-03afc9903e89

import Mathlib
import Definitions.Def_OAIQ098E031

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma transStep_r5_8_eq_e_oai : ∀ k : Fin 16, transStepExpr 5 8 k = transStep_r5_8 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.transStep_r5_8_eq_e_oai := @OAI.SharpPlanar.CachedData.transStep_r5_8_eq_e_oai
