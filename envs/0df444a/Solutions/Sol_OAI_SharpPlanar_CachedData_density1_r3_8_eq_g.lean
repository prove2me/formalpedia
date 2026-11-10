-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r3_8_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:54:22.572469+00:00
-- url     : https://prove2.me/submissions/1b22b60b-2205-41d7-8a6d-d5526e203130

import Mathlib
import Definitions.Def_OAIQ098G397
import Definitions.Def_OAIQ098G404

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel3
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
lemma density1_r3_8_eq_g_oai : ∀ k : Fin 16, density1Expr 3 8 k = density1_r3_8 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r3_8_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r3_8_eq_g_oai
