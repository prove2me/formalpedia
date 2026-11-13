-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.Ckernel_summable_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:40:39.10292+00:00
-- url     : https://prove2.me/submissions/c532c450-f9dc-4a0f-b3e1-b309593f484a

import Mathlib
import Definitions.Def_OAIQ334E002
import Definitions.Def_OAIQ334E003
import Theorems.Thm_OAI_AtomicTriangular_Construction_tail_atom_column_bounds_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
lemma Ckernel_summable_eu_oai (i : Fin 20) : Summable (fun p => |Ckernel p i|) :=
  (tail_atom_column_bounds_eu 1 0 _).1
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.Ckernel_summable_eu_oai := @OAI.AtomicTriangular.Construction.Ckernel_summable_eu_oai
