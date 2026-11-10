-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r5_12_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T17:50:38.131953+00:00
-- url     : https://prove2.me/submissions/68e9ba0f-ad07-429b-abad-06e77b07ffed

import Mathlib
import Definitions.Def_OAIQ098G397
import Definitions.Def_OAIQ098G406

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel5
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
lemma density1_r5_12_eq_g_oai : ∀ k : Fin 16, density1Expr 5 12 k = density1_r5_12 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r5_12_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r5_12_eq_g_oai
