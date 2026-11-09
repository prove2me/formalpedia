-- Prove2me | solution 1 for OAI.SharpPlanar.finiteRestriction_embedding_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:09:10.625826+00:00
-- url     : https://prove2.me/submissions/d11a1e58-04fa-49a5-9fd2-18511cb0f1f5

import Mathlib
import Definitions.Def_OAIQ098G010
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_apply_g

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
lemma finiteRestriction_apply (x : X) (i : ι) : finiteRestriction e he x i = x (e i) := rfl
lemma finiteRestriction_embedding_g_oai (x : L1Finite ι) :
    finiteRestriction e he (finiteEmbedding e x) = x := by
  classical
  ext i
  rw [finiteRestriction_apply,finiteEmbedding_apply_g]
  simp only [he.eq_iff]
  simp
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteRestriction_embedding_g_oai.{u_1} := @OAI.SharpPlanar.finiteRestriction_embedding_g_oai.{u_1}
