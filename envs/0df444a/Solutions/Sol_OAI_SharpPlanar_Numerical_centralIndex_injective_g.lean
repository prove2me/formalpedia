-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.centralIndex_injective_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:07:32.175571+00:00
-- url     : https://prove2.me/submissions/79bf0682-68f7-46fb-b21b-30f6e1cb221e

import Mathlib
import Definitions.Def_OAIQ098G000

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
lemma centralIndex_injective_g_oai : Function.Injective centralIndex := by decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.centralIndex_injective_g_oai := @OAI.SharpPlanar.Numerical.centralIndex_injective_g_oai
