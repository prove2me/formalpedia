-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteIndex_injective_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T08:08:51.637682+00:00
-- url     : https://prove2.me/submissions/ed0d2907-65d9-4b74-8b69-050dd4e4c698

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
lemma finiteIndex_injective_e_oai : Function.Injective finiteIndex := by decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteIndex_injective_e_oai := @OAI.SharpPlanar.Numerical.finiteIndex_injective_e_oai
