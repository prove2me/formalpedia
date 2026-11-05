-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.centralIndex_injective_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T08:04:27.169201+00:00
-- url     : https://prove2.me/submissions/d8de35eb-a77e-42c2-8a3f-4b97156c5d13

import Mathlib
import Definitions.Def_OAIQ098E000

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
lemma centralIndex_injective_e_oai : Function.Injective centralIndex := by decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.centralIndex_injective_e_oai := @OAI.SharpPlanar.Numerical.centralIndex_injective_e_oai
