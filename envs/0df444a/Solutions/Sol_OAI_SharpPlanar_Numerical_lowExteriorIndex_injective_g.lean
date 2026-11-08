-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.lowExteriorIndex_injective_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:58:57.738194+00:00
-- url     : https://prove2.me/submissions/d0865001-4594-4fd0-85a4-e91c9a513532

import Mathlib
import Definitions.Def_OAIQ098G011

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
lemma lowExteriorIndex_injective_g_oai : Function.Injective lowExteriorIndex := by decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.lowExteriorIndex_injective_g_oai := @OAI.SharpPlanar.Numerical.lowExteriorIndex_injective_g_oai
