-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r3_8_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:37:59.722216+00:00
-- url     : https://prove2.me/submissions/60827435-c790-44e7-ba7a-cc7a133a7ae6

import Mathlib
import Definitions.Def_OAIQ098G389
import Definitions.Def_OAIQ098G397

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel3
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
lemma density0_r3_8_eq_g_oai : ∀ k : Fin 16, density0Expr 3 8 k = density0_r3_8 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r3_8_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r3_8_eq_g_oai
