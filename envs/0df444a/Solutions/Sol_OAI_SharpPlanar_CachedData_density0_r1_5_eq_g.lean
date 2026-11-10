-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r1_5_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:23:46.203109+00:00
-- url     : https://prove2.me/submissions/382bd5c7-36af-4edb-8105-96ce4ea3fc95

import Mathlib
import Definitions.Def_OAIQ098G387
import Definitions.Def_OAIQ098G397

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel1
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
lemma density0_r1_5_eq_g_oai : ∀ k : Fin 16, density0Expr 1 5 k = density0_r1_5 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r1_5_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r1_5_eq_g_oai
