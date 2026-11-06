-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteIndex_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:26:57.907208+00:00
-- url     : https://prove2.me/submissions/43c08286-e186-4462-9a55-5e95864f8354

import Mathlib
import Definitions.Def_OAIQ098E007

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
lemma finiteIndex_bound_e_oai (i : FiniteIndex) : (finiteIndex i).1.val ≤ 100 := by revert i; decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteIndex_bound_e_oai := @OAI.SharpPlanar.Numerical.finiteIndex_bound_e_oai
