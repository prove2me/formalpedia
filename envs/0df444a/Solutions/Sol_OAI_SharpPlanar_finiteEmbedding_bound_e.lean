-- Prove2me | solution 1 for OAI.SharpPlanar.finiteEmbedding_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:37:12.241778+00:00
-- url     : https://prove2.me/submissions/e8258982-50e1-4150-b524-8624a29f75fa

import Mathlib
import Definitions.Def_OAIQ098E008
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_e

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
lemma finiteEmbedding_bound_e_oai (x : L1Finite ι) : ‖finiteEmbeddingLinear e x‖ ≤ 1*‖x‖ := by
  rw [one_mul,l1Finite_norm_e]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by simp [lp.norm_single]))
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteEmbedding_bound_e_oai.{u_1} := @OAI.SharpPlanar.finiteEmbedding_bound_e_oai.{u_1}
