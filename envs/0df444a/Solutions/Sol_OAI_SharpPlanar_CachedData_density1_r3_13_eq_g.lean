-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r3_13_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T17:50:29.161179+00:00
-- url     : https://prove2.me/submissions/52aaa6b9-9e85-4e14-9eeb-ad04f0f0d45d

import Mathlib
import Definitions.Def_OAIQ098G397
import Definitions.Def_OAIQ098G402

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
lemma density1_r3_13_eq_g_oai : ∀ k : Fin 16, density1Expr 3 13 k = density1_r3_13 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r3_13_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r3_13_eq_g_oai
