-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r4_5_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:42:21.774192+00:00
-- url     : https://prove2.me/submissions/860ec62c-ba48-4dfc-9d52-04d19972cc41

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
lemma density0_r4_5_eq_g_oai : ∀ k : Fin 16, density0Expr 4 5 k = density0_r4_5 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r4_5_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r4_5_eq_g_oai
