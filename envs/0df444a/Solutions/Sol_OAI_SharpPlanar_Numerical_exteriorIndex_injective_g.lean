-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.exteriorIndex_injective_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:56:26.313354+00:00
-- url     : https://prove2.me/submissions/832818a3-df67-47eb-8e22-1bfe608c7db2

import Mathlib
import Definitions.Def_OAIQ098G006

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
lemma exteriorIndex_injective_g_oai : Function.Injective exteriorIndex := by decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.exteriorIndex_injective_g_oai := @OAI.SharpPlanar.Numerical.exteriorIndex_injective_g_oai
