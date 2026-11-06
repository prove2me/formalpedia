-- Prove2me | solution 1 for OAI.SharpPlanar.finiteRestriction_embedding_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:55:47.677898+00:00
-- url     : https://prove2.me/submissions/d5aae421-7bf6-433e-a75f-887a445b954e

import Mathlib
import Definitions.Def_OAIQ098E010
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_apply_e
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_apply_e

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
lemma finiteRestriction_embedding_e_oai (x : L1Finite ι) :
    finiteRestriction e he (finiteEmbedding e x) = x := by
  classical
  ext i
  rw [finiteRestriction_apply_e,finiteEmbedding_apply_e]
  simp only [he.eq_iff]
  simp
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteRestriction_embedding_e_oai.{u_1} := @OAI.SharpPlanar.finiteRestriction_embedding_e_oai.{u_1}
