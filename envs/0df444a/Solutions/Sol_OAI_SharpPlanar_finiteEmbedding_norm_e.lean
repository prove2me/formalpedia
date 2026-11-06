-- Prove2me | solution 1 for OAI.SharpPlanar.finiteEmbedding_norm_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:55:03.276588+00:00
-- url     : https://prove2.me/submissions/4fa098ad-80c0-4e25-b97c-dff4d9496366

import Mathlib
import Definitions.Def_OAIQ098E010
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_bound_e
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_bound_e
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_embedding_e

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
lemma finiteEmbedding_norm_e_oai (x : L1Finite ι) : ‖finiteEmbedding e x‖ = ‖x‖ := by
  apply le_antisymm
  · exact (finiteEmbedding_bound_e e x).trans_eq (one_mul _)
  · have hh := finiteRestriction_bound_e e he (finiteEmbedding e x)
    change ‖finiteRestriction e he (finiteEmbedding e x)‖ ≤ _ at hh
    simpa only [finiteRestriction_embedding_e,one_mul] using hh
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteEmbedding_norm_e_oai.{u_1} := @OAI.SharpPlanar.finiteEmbedding_norm_e_oai.{u_1}
