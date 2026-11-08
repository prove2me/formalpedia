-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteIndex_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:10:20.308241+00:00
-- url     : https://prove2.me/submissions/fd158d95-c6c8-4d91-85ee-90549cb499f7

import Mathlib
import Definitions.Def_OAIQ098G007

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

open scoped BigOperators
lemma finiteIndex_bound_g_oai (i : FiniteIndex) : (finiteIndex i).1.val ≤ 100 := by revert i; decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteIndex_bound_g_oai := @OAI.SharpPlanar.Numerical.finiteIndex_bound_g_oai
