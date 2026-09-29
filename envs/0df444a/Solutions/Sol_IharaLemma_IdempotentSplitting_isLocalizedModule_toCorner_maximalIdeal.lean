-- Prove2me | solution 1 for IharaLemma.IdempotentSplitting.isLocalizedModule_toCorner_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2d0256c3-526e-5476-b5a9-b4088f6fb108

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Theorems.Thm_IharaLemma_isLocalizedModule_toCorner
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal

open IharaLemma

theorem solution {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n) {M : Type}
    [AddCommGroup M] [Module B M] :
    IsLocalizedModule (S.𝔪 i).primeCompl (toCorner (M := M) (S.e i)) :=
  IharaLemma.isLocalizedModule_toCorner (S.idem i) (S.𝔪 i) (S.notMem i)
    (S.mem_of_isMaximal_of_ne i)

end S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal
end P2MW
export P2MW.S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal (solution)
