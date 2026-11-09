-- Prove2me | solution 1 for OAI.SharpPlanar.finiteEmbedding_apply_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:15.566812+00:00
-- url     : https://prove2.me/submissions/f8aafdb1-a833-4b9d-a1f5-d97880cb4f7e

import Mathlib
import Definitions.Def_OAIQ098G010

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
lemma finiteEmbedding_apply_g_oai (x : L1Finite ι) (i : Node × Bool) :
    finiteEmbedding e x i = ∑ j, if e j=i then x j else 0 := by
  change (∑ j, lp.single 1 (e j) (x j) : X) i = _
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply, eq_comm]
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteEmbedding_apply_g_oai.{u_1} := @OAI.SharpPlanar.finiteEmbedding_apply_g_oai.{u_1}
