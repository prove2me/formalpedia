-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.Ckernel_summable_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:34:45.882204+00:00
-- url     : https://prove2.me/submissions/fe1b6932-872f-4b44-acee-49be716e4de9

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X002
import Definitions.Def_OAIQ257X003
import Theorems.Thm_OAI_AtomicTriangular_Construction_tail_atom_column_bounds_x

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
lemma Ckernel_summable_x_oai (i : Fin 20) : Summable (fun p => |Ckernel p i|) :=
  (tail_atom_column_bounds_x 1 0 _).1
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.Ckernel_summable_x_oai := @OAI.AtomicTriangular.Construction.Ckernel_summable_x_oai
