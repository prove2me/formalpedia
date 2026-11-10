-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r2_8_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T17:50:24.639909+00:00
-- url     : https://prove2.me/submissions/f0bdfcc0-c245-4701-8031-43f797d58e27

import Mathlib
import Definitions.Def_OAIQ098G397
import Definitions.Def_OAIQ098G402

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel2
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
lemma density1_r2_8_eq_g_oai : ∀ k : Fin 16, density1Expr 2 8 k = density1_r2_8 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r2_8_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r2_8_eq_g_oai
