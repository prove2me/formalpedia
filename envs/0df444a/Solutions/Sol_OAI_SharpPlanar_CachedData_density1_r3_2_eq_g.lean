-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r3_2_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:53:02.204043+00:00
-- url     : https://prove2.me/submissions/d820c219-cc8a-46fb-b281-ac4d15a53340

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
lemma density1_r3_2_eq_g_oai : ∀ k : Fin 16, density1Expr 3 2 k = density1_r3_2 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r3_2_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r3_2_eq_g_oai
