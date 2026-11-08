-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteIndex_injective_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:12:20.403204+00:00
-- url     : https://prove2.me/submissions/d51a4ca1-026d-4e29-899b-273482199136

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
lemma finiteIndex_injective_g_oai : Function.Injective finiteIndex := by decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteIndex_injective_g_oai := @OAI.SharpPlanar.Numerical.finiteIndex_injective_g_oai
