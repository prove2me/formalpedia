-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.transStep_r3_0_eq_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T01:12:43.835716+00:00
-- url     : https://prove2.me/submissions/8ac94383-4325-4c9b-b887-ffc59d1bc368

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
lemma transStep_r3_0_eq_e_oai : ∀ k : Fin 16, transStepExpr 3 0 k = transStep_r3_0 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.transStep_r3_0_eq_e_oai := @OAI.SharpPlanar.CachedData.transStep_r3_0_eq_e_oai
