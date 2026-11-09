-- Prove2me | solution 1 for OAI.SharpPlanar.finiteEmbedding_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:34:41.11239+00:00
-- url     : https://prove2.me/submissions/9896ad1a-39cd-4680-a050-6fb7a098fae9

import Mathlib
import Definitions.Def_OAIQ098G008
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_g

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
lemma finiteEmbedding_bound_g_oai (x : L1Finite ι) : ‖finiteEmbeddingLinear e x‖ ≤ 1*‖x‖ := by
  rw [one_mul,l1Finite_norm_g]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by simp [lp.norm_single]))
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteEmbedding_bound_g_oai.{u_1} := @OAI.SharpPlanar.finiteEmbedding_bound_g_oai.{u_1}
