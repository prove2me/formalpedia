-- Prove2me | solution 1 for OAI.SharpPlanar.finiteEmbedding_norm_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:16.884452+00:00
-- url     : https://prove2.me/submissions/bf2e21e5-b076-468c-bbb2-c9ae2cce7dcd

import Mathlib
import Definitions.Def_OAIQ098G010
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_bound_g
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_bound_g
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_embedding_g

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
include he in
lemma finiteEmbedding_norm_g_oai (x : L1Finite ι) : ‖finiteEmbedding e x‖ = ‖x‖ := by
  apply le_antisymm
  · exact (finiteEmbedding_bound_g e x).trans_eq (one_mul _)
  · have hh := finiteRestriction_bound_g e he (finiteEmbedding e x)
    change ‖finiteRestriction e he (finiteEmbedding e x)‖ ≤ _ at hh
    simpa only [finiteRestriction_embedding_g,one_mul] using hh
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteEmbedding_norm_g_oai.{u_1} := @OAI.SharpPlanar.finiteEmbedding_norm_g_oai.{u_1}
