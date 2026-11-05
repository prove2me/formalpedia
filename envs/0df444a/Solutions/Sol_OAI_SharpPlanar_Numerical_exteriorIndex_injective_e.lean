-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.exteriorIndex_injective_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T08:05:56.855205+00:00
-- url     : https://prove2.me/submissions/63d4366e-479b-4564-aa38-c564a63bebaa

import Mathlib
import Definitions.Def_OAIQ098E006

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
lemma exteriorIndex_injective_e_oai : Function.Injective exteriorIndex := by decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.exteriorIndex_injective_e_oai := @OAI.SharpPlanar.Numerical.exteriorIndex_injective_e_oai
