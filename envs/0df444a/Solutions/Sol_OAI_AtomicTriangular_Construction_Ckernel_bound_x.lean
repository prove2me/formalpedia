-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.Ckernel_bound_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:31:28.460649+00:00
-- url     : https://prove2.me/submissions/bc3dbace-e68c-47c8-a9cb-186cfcddc9a6

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X002
import Theorems.Thm_OAI_AtomicTriangular_Construction_tail_finite_column_bound_x

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
lemma Ckernel_bound_x_oai (i : Fin 20) : (∑' p, |Ckernel p i|) ≤ 7/10^15 :=
  (tail_finite_column_bound_x ⟨i.val+2,by omega⟩).le
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.Ckernel_bound_x_oai := @OAI.AtomicTriangular.Construction.Ckernel_bound_x_oai
