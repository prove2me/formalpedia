-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r5_15_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:43:11.959365+00:00
-- url     : https://prove2.me/submissions/2df8b8fe-ca69-4786-b79f-34fcf9e5c324

import Mathlib
import Definitions.Def_OAIQ098G391
import Definitions.Def_OAIQ098G397

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel5
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
open IntegerIntervals IntegerBasis IntegerGrid
lemma density0_r5_15_eq_g_oai : ∀ k : Fin 16, density0Expr 5 15 k = density0_r5_15 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r5_15_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r5_15_eq_g_oai
