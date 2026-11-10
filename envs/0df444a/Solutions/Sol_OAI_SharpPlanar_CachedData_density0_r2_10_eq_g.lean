-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r2_10_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:23:05.856325+00:00
-- url     : https://prove2.me/submissions/7c27e9a6-f01f-4ecb-b7c2-fc5161ff8123

import Mathlib
import Definitions.Def_OAIQ098G388
import Definitions.Def_OAIQ098G397

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel2
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
lemma density0_r2_10_eq_g_oai : ∀ k : Fin 16, density0Expr 2 10 k = density0_r2_10 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r2_10_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r2_10_eq_g_oai
