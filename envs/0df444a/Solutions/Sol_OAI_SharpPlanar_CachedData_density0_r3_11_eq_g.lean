-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r3_11_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T17:46:09.351552+00:00
-- url     : https://prove2.me/submissions/08567382-60f6-419e-8beb-0fa73e6b0c06

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
lemma density0_r3_11_eq_g_oai : ∀ k : Fin 16, density0Expr 3 11 k = density0_r3_11 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r3_11_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r3_11_eq_g_oai
