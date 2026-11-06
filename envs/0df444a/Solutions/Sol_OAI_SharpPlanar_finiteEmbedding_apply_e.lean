-- Prove2me | solution 1 for OAI.SharpPlanar.finiteEmbedding_apply_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:55:02.239229+00:00
-- url     : https://prove2.me/submissions/3a5b1cb3-165a-44da-8706-7dc65672c3b9

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
lemma finiteEmbedding_apply_e_oai (x : L1Finite ι) (i : Node × Bool) :
    finiteEmbedding e x i = ∑ j, if e j=i then x j else 0 := by
  change (∑ j, lp.single 1 (e j) (x j) : X) i = _
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply, eq_comm]
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteEmbedding_apply_e_oai.{u_1} := @OAI.SharpPlanar.finiteEmbedding_apply_e_oai.{u_1}
