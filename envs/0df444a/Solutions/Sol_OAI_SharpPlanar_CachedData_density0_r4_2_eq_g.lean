-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r4_2_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:38:13.310479+00:00
-- url     : https://prove2.me/submissions/2ce4ceef-9eaa-44a4-b6de-d2da4b2710ac

import Mathlib
import Definitions.Def_OAIQ098G390
import Definitions.Def_OAIQ098G397

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel4
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
lemma density0_r4_2_eq_g_oai : ∀ k : Fin 16, density0Expr 4 2 k = density0_r4_2 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r4_2_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r4_2_eq_g_oai
