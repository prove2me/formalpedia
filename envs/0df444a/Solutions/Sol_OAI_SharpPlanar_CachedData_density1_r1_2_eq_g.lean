-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r1_2_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:49:33.465606+00:00
-- url     : https://prove2.me/submissions/dde0cc5e-b1eb-4ddf-8f65-28184cdd9dbf

import Mathlib
import Definitions.Def_OAIQ098G397
import Definitions.Def_OAIQ098G398

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel1
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
lemma density1_r1_2_eq_g_oai : ∀ k : Fin 16, density1Expr 1 2 k = density1_r1_2 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r1_2_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r1_2_eq_g_oai
