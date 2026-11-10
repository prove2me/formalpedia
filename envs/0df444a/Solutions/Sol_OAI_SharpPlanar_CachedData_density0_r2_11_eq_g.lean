-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r2_11_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:23:48.198795+00:00
-- url     : https://prove2.me/submissions/be1739de-d46c-423d-8a5e-058428bf7ec1

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
lemma density0_r2_11_eq_g_oai : ∀ k : Fin 16, density0Expr 2 11 k = density0_r2_11 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r2_11_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r2_11_eq_g_oai
