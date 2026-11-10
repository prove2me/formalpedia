-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r0_3_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:45:43.885732+00:00
-- url     : https://prove2.me/submissions/ad8a3391-5b86-4af0-9b4f-8f80c29a58b6

import Mathlib
import Definitions.Def_OAIQ098G393
import Definitions.Def_OAIQ098G397

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel0
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
lemma density1_r0_3_eq_g_oai : ∀ k : Fin 16, density1Expr 0 3 k = density1_r0_3 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r0_3_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r0_3_eq_g_oai
