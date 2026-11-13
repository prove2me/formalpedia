-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.Ckernel_bound_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:43:39.327366+00:00
-- url     : https://prove2.me/submissions/049c9c04-fc8f-4a08-825d-4b74a6e61284

import Mathlib
import Definitions.Def_OAIQ334E002
import Theorems.Thm_OAI_AtomicTriangular_Construction_tail_finite_column_bound_eu

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
lemma Ckernel_bound_eu_oai (i : Fin 20) : (∑' p, |Ckernel p i|) ≤ 7/10^15 :=
  (tail_finite_column_bound_eu ⟨i.val+2,by omega⟩).le
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.Ckernel_bound_eu_oai := @OAI.AtomicTriangular.Construction.Ckernel_bound_eu_oai
