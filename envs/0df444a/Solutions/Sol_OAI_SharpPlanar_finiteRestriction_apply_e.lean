-- Prove2me | solution 1 for OAI.SharpPlanar.finiteRestriction_apply_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:55:25.447011+00:00
-- url     : https://prove2.me/submissions/138fdc08-c619-4662-9d95-616575422c5d

import Mathlib
import Definitions.Def_OAIQ098E010

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_apply_e_oai (x : X) (i : ι) : finiteRestriction e he x i = x (e i) := rfl
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteRestriction_apply_e_oai.{u_1} := @OAI.SharpPlanar.finiteRestriction_apply_e_oai.{u_1}
